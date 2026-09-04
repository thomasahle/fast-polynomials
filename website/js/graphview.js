// SVG rendering of the computational-graph IR (see graph.js).
//
//   renderGraphSVG(graph, { theme }) -> SVG string (self-contained, no libraries)
//   layoutGraph(graph)               -> { pos: Map<id,{x,y,w,h}>, width, height, layers }
//   graphToText(graph)               -> compact textual DAG listing (fallback)
//
// Layout: layered DAG, left-to-right (Sugiyama-style).  Longest-path layering
// from the sources (single-use constants are pulled next to their consumer);
// edges spanning >1 layer are virtualized through zero-size waypoints (plain
// edges from one source share a "trunk" rail, so hubs such as x fan out as one
// bus); barycenter ordering with a few down/up sweeps plus a crossing-reducing
// transpose pass; then a neighbour-mean coordinate assignment with overlap
// resolution.  Long edges are drawn through their waypoints, so they follow
// the computed order instead of sweeping across the picture.
// countCrossings(graph) reports the exact number of pairwise edge-segment
// crossings of the drawn layout.  Nodes: '*' filled circles, '+' outlined
// circles, x / constants as small rounded boxes, output highlighted.  Edges are
// cubic curves with arrowheads; subtracted inputs are dashed and marked '−',
// integer multiples carry a 'k×' label.  Colors come from the page's CSS
// variables (--accent, --ink, --border, --mono-bg, --muted, --panel,
// --accent-soft) with light/dark fallbacks chosen by opts.theme.

const R = 13;             // operator-node radius
const ROW_GAP = 44;       // vertical distance between node centres in a layer
const VGAP = 16;          // vertical separation reserved for a routed edge rail
const LAYER_GAP = 58;     // horizontal gap between layer boxes
const MARGIN = 26;
const CHAR_W = 7.2;       // approx. width of a 12px monospace glyph
const MAX_LABEL = 16;

const esc = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');

function nodeSize(n) {
  if (n.kind === 'mul' || n.kind === 'add') return { w: 2 * R, h: 2 * R };
  if (n.kind === 'out') return { w: Math.max(34, n.label.length * CHAR_W + 18), h: 30 };
  const s = shortLabel(n.label);
  return { w: Math.max(26, s.length * CHAR_W + 14), h: 24 };
}
function shortLabel(s) {
  s = String(s);
  return s.length > MAX_LABEL ? s.slice(0, MAX_LABEL - 1) + '…' : s;
}

/** Layered layout. Returns { pos, width, height, layers, routes }.
 *
 * Sugiyama-style pipeline:
 *   1. longest-path layering; single-consumer constants move next to their
 *      consumer.
 *   2. edge virtualization: an edge spanning >1 layer runs through one
 *      zero-size virtual waypoint per intermediate layer, so the ordering
 *      phase sees it.  Plain edges from the same source share their
 *      waypoints (a "trunk"): a fan-out hub such as x becomes one rail that
 *      peels off a branch per consumer.  Negated / labelled edges keep
 *      private waypoints so their dashes and labels stay legible.
 *   3. ordering: barycenter down/up sweeps over the augmented graph, then a
 *      transpose pass — adjacent nodes in a layer are swapped whenever that
 *      strictly reduces the exact crossing count.
 *   4. coordinates: x per layer (widest real node); y by neighbour means
 *      with overlap resolution.  Operator nodes need ROW_GAP, virtual rails
 *      only VGAP; leaves (constants, x) take the nearest free slot.
 *
 * routes[i] lists the waypoints {x, y, layer} of edges[i] (null for edges
 * spanning one layer); renderGraphSVG and countCrossings both follow them.
 */
export function layoutGraph(graph) {
  const nodes = graph.nodes, edges = graph.edges;
  const N = nodes.length;
  const idx = new Map(nodes.map((n, i) => [n.id, i]));
  const preds = nodes.map(() => []), succs = nodes.map(() => []);
  for (const e of edges) {
    const a = idx.get(e.from), b = idx.get(e.to);
    if (a === undefined || b === undefined) throw new Error(`graph: edge on unknown node ${e.from} -> ${e.to}`);
    preds[b].push(a); succs[a].push(b);
  }
  // topological order (Kahn) — also detects cycles
  const indeg = preds.map(p => p.length);
  const order = [];
  const queue = [];
  for (let i = 0; i < N; i++) if (indeg[i] === 0) queue.push(i);
  while (queue.length) {
    const u = queue.shift(); order.push(u);
    for (const v of succs[u]) if (--indeg[v] === 0) queue.push(v);
  }
  if (order.length !== N) throw new Error('graph: cycle detected');

  // longest-path layering
  const layer = new Array(N).fill(0);
  for (const u of order) for (const v of succs[u]) layer[v] = Math.max(layer[v], layer[u] + 1);
  // pull single-consumer leaves (constants) next to their consumer
  for (let i = 0; i < N; i++)
    if (preds[i].length === 0 && succs[i].length >= 1 && nodes[i].kind !== 'x') {
      const m = Math.min(...succs[i].map(v => layer[v]));
      layer[i] = Math.max(0, m - 1);
    }
  const L = Math.max(0, ...layer) + 1;

  // edge virtualization (nodes N.. are virtual waypoints; unit-span links only)
  const aLayer = layer.slice();
  const aPreds = nodes.map(() => []), aSuccs = nodes.map(() => []);
  const newV = l => { aLayer.push(l); aPreds.push([]); aSuccs.push([]); return aLayer.length - 1; };
  const link = (u, v) => { aSuccs[u].push(v); aPreds[v].push(u); };
  const trunks = new Map();                    // source -> shared waypoints at layer+1, layer+2, …
  const routeIdx = edges.map(() => null);      // per edge: its waypoint node indices
  edges.forEach((e, i) => {
    const a = idx.get(e.from), b = idx.get(e.to);
    if (aLayer[b] - aLayer[a] <= 1) { link(a, b); return; }
    let chain;
    if (e.neg || e.label) {                    // private waypoints: dash / label stays its own curve
      chain = [];
      let prev = a;
      for (let l = aLayer[a] + 1; l < aLayer[b]; l++) { const v = newV(l); link(prev, v); chain.push(v); prev = v; }
      link(prev, b);
    } else {                                   // shared trunk rail from this source
      const t = trunks.get(a) ?? [];
      while (aLayer[a] + 1 + t.length < aLayer[b]) {
        const v = newV(aLayer[a] + 1 + t.length);
        link(t.length ? t[t.length - 1] : a, v);
        t.push(v);
      }
      trunks.set(a, t);
      chain = t.slice(0, aLayer[b] - aLayer[a] - 1);
      link(chain[chain.length - 1], b);
    }
    routeIdx[i] = chain;
  });
  const A = aLayer.length;
  const layers = Array.from({ length: L }, () => []);
  for (const u of order) layers[layer[u]].push(u);
  for (let v = N; v < A; v++) layers[aLayer[v]].push(v);

  // ordering: barycenter down/up sweeps alternated with a transpose pass
  // (adjacent swaps kept only when they strictly reduce the exact crossing
  // count against both neighbouring layers); the best ordering seen wins
  const posIn = new Array(A).fill(0);
  const setPos = l => l.forEach((u, i) => { posIn[u] = i; });
  layers.forEach(setPos);
  const bary = (u, nb) => (nb.length ? nb.reduce((s, v) => s + posIn[v], 0) / nb.length : posIn[u]);
  const median = (u, nb) => {
    if (!nb.length) return posIn[u];
    const p = nb.map(v => posIn[v]).sort((a, b) => a - b);
    const m = p.length >> 1;
    return p.length % 2 ? p[m] : (p[m - 1] + p[m]) / 2;
  };
  const downUp = key => {
    for (let l = 1; l < L; l++) {
      const keyed = layers[l].map(u => [key(u, aPreds[u]), posIn[u], u]);
      keyed.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
      layers[l] = keyed.map(k => k[2]); setPos(layers[l]);
    }
    for (let l = L - 2; l >= 0; l--) {
      const keyed = layers[l].map(u => [key(u, aSuccs[u]), posIn[u], u]);
      keyed.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
      layers[l] = keyed.map(k => k[2]); setPos(layers[l]);
    }
  };
  // unit links per layer pair, weighted by how many edges ride them (a trunk
  // link shared by k edges costs k per crossing — exactly the drawn count)
  const segMaps = Array.from({ length: Math.max(0, L - 1) }, () => new Map());
  edges.forEach((e, i) => {
    const path = [idx.get(e.from), ...(routeIdx[i] ?? []), idx.get(e.to)];
    for (let j = 0; j + 1 < path.length; j++) {
      const m = segMaps[aLayer[path[j]]], k = path[j] * A + path[j + 1];
      m.set(k, (m.get(k) ?? 0) + 1);
    }
  });
  const segs = segMaps.map(m => [...m.entries()].map(([k, w]) => [Math.floor(k / A), k % A, w]));
  // crossW weighs each pair by edge multiplicity — it IS the drawn crossing
  // count; crossU (every link once) explores different local optima
  const mkCross = weighted => l => {
    if (l < 0 || l >= L - 1) return 0;
    const S = segs[l];
    let c = 0;
    for (let i = 0; i < S.length; i++)
      for (let j = i + 1; j < S.length; j++)
        if ((posIn[S[i][0]] - posIn[S[j][0]]) * (posIn[S[i][1]] - posIn[S[j][1]]) < 0) c += weighted ? S[i][2] * S[j][2] : 1;
    return c;
  };
  const crossW = mkCross(true), crossU = mkCross(false);
  const transpose = cross => {
    for (let pass = 0, improved = true; improved && pass < 10; pass++) {
      improved = false;
      for (let l = 0; l < L; l++) {
        const row = layers[l];
        for (let i = 0; i + 1 < row.length; i++) {
          const before = cross(l - 1) + cross(l);
          [row[i], row[i + 1]] = [row[i + 1], row[i]];
          posIn[row[i]] = i; posIn[row[i + 1]] = i + 1;
          if (cross(l - 1) + cross(l) < before) improved = true;
          else { [row[i], row[i + 1]] = [row[i + 1], row[i]]; posIn[row[i]] = i; posIn[row[i + 1]] = i + 1; }
        }
      }
    }
  };
  const totalCross = () => { let c = 0; for (let l = 0; l < L - 1; l++) c += crossW(l); return c; };
  let bestCount = Infinity, bestOrd = null;
  const consider = () => { const t = totalCross(); if (t < bestCount) { bestCount = t; bestOrd = layers.map(r => r.slice()); } };
  downUp(bary); downUp(bary); consider();
  for (const key of [bary, median, bary, median]) {
    transpose(crossU); consider();
    transpose(crossW); consider();
    downUp(key); consider();
  }
  transpose(crossU); consider();
  transpose(crossW); consider();
  for (let l = 0; l < L; l++) layers[l] = bestOrd[l];
  layers.forEach(setPos);

  // coordinates: x per layer (by widest real node), y by neighbour means with
  // overlap resolution; virtual waypoints only reserve VGAP instead of ROW_GAP
  const size = nodes.map(nodeSize);
  const sep = u => (u < N ? ROW_GAP : VGAP);
  const layerW = layers.map(l => Math.max(10, ...l.filter(u => u < N).map(u => size[u].w)));
  const layerX = [];
  let x = MARGIN;
  for (let l = 0; l < L; l++) {
    x += layerW[l] / 2;
    layerX.push(x);
    x += layerW[l] / 2 + LAYER_GAP;
  }
  const y = new Array(A).fill(0);
  layers.forEach(l => { let cur = 0; l.forEach((u, i) => { cur += i ? (sep(l[i - 1]) + sep(u)) / 2 : 0; y[u] = cur; }); });
  // y assignment NEVER reorders a layer — the crossing-minimized order is
  // final; each pass only pulls nodes towards the mean of their neighbours on
  // the sweep side (falling back to the other side for leaves / the sink),
  // restores the pairwise separation with a forward max-pass, and recentres
  // the layer on its non-leaf nodes.
  // Leaf inputs (constants) do not pull: an operator with a constant and a
  // wire input aligns with the wire, and the constant hangs beside it —
  // otherwise every 'wire + const' stage would step sideways by half a row.
  const isLeaf = v => aPreds[v].length === 0;
  const wmean = (u, nb) => {
    const core = nb.filter(v => !isLeaf(v));
    const use = core.length ? core : nb;
    return use.length ? use.reduce((s, v) => s + y[v], 0) / use.length : y[u];
  };
  const place = (l, nb, other) => {
    const wish = l.map(u => wmean(u, nb(u).length ? nb(u) : other(u)));
    const got = [];
    let cur = 0;
    l.forEach((u, i) => { cur = i ? Math.max(cur + (sep(l[i - 1]) + sep(u)) / 2, wish[i]) : wish[0]; got.push(cur); });
    const core = l.map((u, i) => i).filter(i => !isLeaf(l[i]));
    const use = core.length ? core : l.map((u, i) => i);
    const shift = use.reduce((s, i) => s + (wish[i] - got[i]), 0) / use.length;
    l.forEach((u, i) => { y[u] = got[i] + shift; });
  };
  for (let it = 0; it < 3; it++) {
    for (let l = 1; l < L; l++) place(layers[l], u => aPreds[u], u => aSuccs[u]);
    for (let l = L - 2; l >= 0; l--) place(layers[l], u => aSuccs[u], u => aPreds[u]);
  }
  const minY = Math.min(...y);
  const pos = new Map();
  let maxY = 0;
  nodes.forEach((n, i) => {
    const yy = y[i] - minY + MARGIN + 14;   // +14: room for wire-name labels above nodes
    pos.set(n.id, { x: layerX[layer[i]], y: yy, w: size[i].w, h: size[i].h, layer: layer[i] });
    maxY = Math.max(maxY, yy + size[i].h / 2);
  });
  for (let v = N; v < A; v++) maxY = Math.max(maxY, y[v] - minY + MARGIN + 14 + VGAP / 2);
  const routes = routeIdx.map(chain => chain &&
    chain.map(v => ({ x: layerX[aLayer[v]], y: y[v] - minY + MARGIN + 14, layer: aLayer[v] })));
  const width = Math.ceil(x - LAYER_GAP + MARGIN);
  const height = Math.ceil(maxY + MARGIN);
  return { pos, width, height, layers: layers.map(l => l.filter(u => u < N).map(u => nodes[u].id)), routes };
}

/** Exact crossing count of the drawn layout.
 * Every edge is virtualized into unit-layer segments: an edge from layer a to
 * layer b contributes segments (a,a+1), (a+1,a+2), …, (b−1,b), with the y at
 * the intermediate layers taken from the layout's routed waypoints when
 * present, else interpolated linearly.  Two segments between the same pair of
 * consecutive layers cross iff their endpoint orders invert (strictly — shared
 * endpoints and coincident bundled segments do not count). */
export function countCrossings(graph, layout = layoutGraph(graph)) {
  const { pos, routes } = layout;
  const segs = new Map();                       // left layer -> [[yLeft, yRight], ...]
  const put = (l, y1, y2) => { const b = segs.get(l) ?? []; b.push([y1, y2]); segs.set(l, b); };
  graph.edges.forEach((e, i) => {
    const a = pos.get(e.from), b = pos.get(e.to);
    const pts = [[a.layer, a.y]];
    const via = routes?.[i];
    if (via && via.length) for (const p of via) pts.push([p.layer, p.y]);
    else for (let l = a.layer + 1; l < b.layer; l++)
      pts.push([l, a.y + (b.y - a.y) * (l - a.layer) / (b.layer - a.layer)]);
    pts.push([b.layer, b.y]);
    for (let k = 0; k + 1 < pts.length; k++) put(pts[k][0], pts[k][1], pts[k + 1][1]);
  });
  let c = 0;
  for (const list of segs.values())
    for (let i = 0; i < list.length; i++)
      for (let j = i + 1; j < list.length; j++)
        if ((list[i][0] - list[j][0]) * (list[i][1] - list[j][1]) < 0) c++;
  return c;
}

const THEMES = {
  light: { ink: '#1c1b18', muted: '#6f6a5e', accent: '#8a4b2d', soft: '#f2e4da', border: '#e2ddd2', mono: '#fbfaf7', panel: '#ffffff', good: '#2e6e4e' },
  dark:  { ink: '#ece8e0', muted: '#9d968a', accent: '#d69a71', soft: '#3a2c22', border: '#383430', mono: '#1d1c1a', panel: '#211f1d', good: '#7fc9a2' },
};

const fmt = v => (Math.round(v * 100) / 100).toString();

/** Render the IR as an SVG string. opts.theme: 'light' (default) | 'dark' picks the var() fallbacks. */
export function renderGraphSVG(graph, { theme = 'light' } = {}) {
  const T = THEMES[theme] ?? THEMES.light;
  const C = {
    ink: `var(--ink, ${T.ink})`, muted: `var(--muted, ${T.muted})`, accent: `var(--accent, ${T.accent})`,
    soft: `var(--accent-soft, ${T.soft})`, border: `var(--border, ${T.border})`, mono: `var(--mono-bg, ${T.mono})`,
    panel: `var(--panel, ${T.panel})`, good: `var(--good, ${T.good})`,
  };
  const { pos, width, height, routes } = layoutGraph(graph);
  const byId = new Map(graph.nodes.map(n => [n.id, n]));
  const out = [];
  out.push(`<svg xmlns="http://www.w3.org/2000/svg" class="graph-svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}" role="img" aria-label="computational graph" style="display:block;max-width:none;font:12px ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;color:${C.ink}">`);
  out.push('<defs>' +
    `<marker id="gv-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" markerUnits="userSpaceOnUse" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" style="fill:${C.muted}"/></marker>` +
    '</defs>');
  out.push(`<title>computational graph: ${graph.nodes.filter(n => n.kind === 'mul').length} multiplications, ${graph.nodes.filter(n => n.kind === 'add').length} additions</title>`);

  // edges (drawn first, under the nodes); long edges follow their layout
  // waypoints as chained cubics with horizontal tangents, so a bundled rail
  // renders as one smooth bus line
  const seen = new Map();          // parallel-edge counter per (from,to)
  out.push(`<g style="fill:none;stroke:${C.muted};stroke-width:1.4">`);
  graph.edges.forEach((e, ei) => {
    const a = pos.get(e.from), b = pos.get(e.to);
    const key = `${e.from}→${e.to}`;
    const k = seen.get(key) ?? 0; seen.set(key, k + 1);
    const x1 = a.x + a.w / 2, y1 = a.y, x2 = b.x - b.w / 2 - 1, y2 = b.y;
    const bend = k === 0 ? 0 : (k % 2 ? 1 : -1) * Math.ceil(k / 2) * 16;   // separate parallel edges
    const via = routes?.[ei];
    let d, mx, my;
    if (via && via.length) {
      const pts = [[x1, y1], ...via.map(p => [p.x, p.y + bend]), [x2, y2]];
      d = `M${fmt(x1)},${fmt(y1)}`;
      for (let i = 1; i < pts.length; i++) {
        const [px, py] = pts[i - 1], [qx, qy] = pts[i];
        const ddx = Math.max(12, (qx - px) * 0.4);
        d += ` C${fmt(px + ddx)},${fmt(py)} ${fmt(qx - ddx)},${fmt(qy)} ${fmt(qx)},${fmt(qy)}`;
      }
      [mx, my] = pts[pts.length >> 1];       // label sits on the middle waypoint
    } else {
      const dx = Math.max(24, (x2 - x1) * 0.5);
      const c1y = y1 + bend, c2y = y2 + bend;
      d = `M${fmt(x1)},${fmt(y1)} C${fmt(x1 + dx)},${fmt(c1y)} ${fmt(x2 - dx)},${fmt(c2y)} ${fmt(x2)},${fmt(y2)}`;
      // point at t = 0.5 of the cubic
      mx = (x1 + 3 * (x1 + dx) + 3 * (x2 - dx) + x2) / 8;
      my = (y1 + 3 * c1y + 3 * c2y + y2) / 8;
    }
    const dash = e.neg ? ';stroke-dasharray:5 3' : '';
    out.push(`<path d="${d}" marker-end="url(#gv-arrow)" style="stroke:${C.muted}${dash}"/>`);
    const label = (e.neg ? '−' : '') + (e.label ?? '');
    if (label)
      out.push(`<text x="${fmt(mx)}" y="${fmt(my - 4)}" text-anchor="middle" style="fill:${C.ink};stroke:${C.panel};stroke-width:3px;paint-order:stroke;font-size:11px">${esc(label)}</text>`);
  });
  out.push('</g>');

  // nodes
  out.push('<g>');
  for (const n of graph.nodes) {
    const p = pos.get(n.id);
    const title = n.wire && n.wire !== n.label ? `${n.wire} = ${n.label}` : n.label;
    let body;
    if (n.kind === 'mul') {
      body = `<circle cx="${fmt(p.x)}" cy="${fmt(p.y)}" r="${R}" style="fill:${C.accent};stroke:${C.accent};stroke-width:1.5"/>` +
             `<text x="${fmt(p.x)}" y="${fmt(p.y + 5)}" text-anchor="middle" style="fill:${C.panel};font-size:15px;font-weight:700">×</text>`;
    } else if (n.kind === 'add') {
      body = `<circle cx="${fmt(p.x)}" cy="${fmt(p.y)}" r="${R}" style="fill:${C.panel};stroke:${C.ink};stroke-width:1.5"/>` +
             `<text x="${fmt(p.x)}" y="${fmt(p.y + 5)}" text-anchor="middle" style="fill:${C.ink};font-size:16px;font-weight:600">+</text>`;
    } else if (n.kind === 'out') {
      body = `<rect x="${fmt(p.x - p.w / 2)}" y="${fmt(p.y - p.h / 2)}" width="${fmt(p.w)}" height="${fmt(p.h)}" rx="8" style="fill:${C.soft};stroke:${C.accent};stroke-width:2.5"/>` +
             `<text x="${fmt(p.x)}" y="${fmt(p.y + 5)}" text-anchor="middle" style="fill:${C.accent};font-size:14px;font-weight:700">${esc(n.label)}</text>`;
    } else if (n.kind === 'x') {
      body = `<rect x="${fmt(p.x - p.w / 2)}" y="${fmt(p.y - p.h / 2)}" width="${fmt(p.w)}" height="${fmt(p.h)}" rx="6" style="fill:${C.soft};stroke:${C.accent};stroke-width:1.5"/>` +
             `<text x="${fmt(p.x)}" y="${fmt(p.y + 4.5)}" text-anchor="middle" style="fill:${C.accent};font-style:italic;font-size:13px;font-weight:700">${esc(n.label)}</text>`;
    } else if (n.kind === 'wire') {
      body = `<rect x="${fmt(p.x - p.w / 2)}" y="${fmt(p.y - p.h / 2)}" width="${fmt(p.w)}" height="${fmt(p.h)}" rx="6" style="fill:${C.panel};stroke:${C.muted};stroke-width:1.2;stroke-dasharray:3 2"/>` +
             `<text x="${fmt(p.x)}" y="${fmt(p.y + 4.5)}" text-anchor="middle" style="fill:${C.ink}">${esc(shortLabel(n.label))}</text>`;
    } else { // const
      body = `<rect x="${fmt(p.x - p.w / 2)}" y="${fmt(p.y - p.h / 2)}" width="${fmt(p.w)}" height="${fmt(p.h)}" rx="6" style="fill:${C.mono};stroke:${C.border};stroke-width:1.2"/>` +
             `<text x="${fmt(p.x)}" y="${fmt(p.y + 4.5)}" text-anchor="middle" style="fill:${C.ink}">${esc(shortLabel(n.label))}</text>`;
    }
    let name = '';
    if (n.wire && (n.kind === 'mul' || n.kind === 'add'))
      name = `<text x="${fmt(p.x)}" y="${fmt(p.y - R - 4)}" text-anchor="middle" style="fill:${C.muted};font-size:11px;font-style:italic">${esc(n.wire)}</text>`;
    out.push(`<g class="gv-node gv-${n.kind}" data-id="${esc(n.id)}"><title>${esc(title)}</title>${body}${name}</g>`);
  }
  out.push('</g>');
  out.push('</svg>');
  return out.join('\n');
}

/** Compact textual DAG listing: one row per named node (wire / output), with
 * anonymous single-use sub-expressions inlined, e.g. `z  ×  (x + y + 5), (−x + y)`. */
export function graphToText(graph) {
  const byId = new Map(graph.nodes.map(n => [n.id, n]));
  const inputs = new Map(graph.nodes.map(n => [n.id, []]));
  const uses = new Map(graph.nodes.map(n => [n.id, 0]));
  for (const e of graph.edges) { inputs.get(e.to).push(e); uses.set(e.from, uses.get(e.from) + 1); }
  const inline = n => n.wire === undefined && (n.kind === 'add' || n.kind === 'mul') && uses.get(n.id) === 1;
  const deco = e => (e.neg ? '−' : '') + (e.label ?? '');
  const expr = n => {                        // inline expression for an anonymous node
    if (n.kind === 'add') return '(' + inputs.get(n.id).map(e => deco(e) + ref(e.from)).join(' + ').replace(/\+ −/g, '− ') + ')';
    return '(' + inputs.get(n.id).map(e => deco(e) + ref(e.from)).join(' × ') + ')';
  };
  const ref = id => {
    const n = byId.get(id);
    if (n.kind === 'x' || n.kind === 'const') return n.label;
    if (inline(n)) return expr(n);
    return n.wire ?? n.id;
  };
  const glyph = { mul: '×', add: '+', out: '=', wire: '=' };
  const rows = [];
  let w = 0;
  for (const n of graph.nodes) {
    if (n.kind === 'x' || n.kind === 'const' || inline(n)) continue;
    const ins = inputs.get(n.id);
    if (n.kind === 'out' && ins.length === 1 && byId.get(ins[0].from).wire === n.label) continue; // already named
    const lhs = n.wire ?? (n.kind === 'out' ? n.label : n.id);
    w = Math.max(w, lhs.length);
    rows.push([lhs, `${glyph[n.kind]}  ${ins.map(e => deco(e) + ref(e.from)).join(', ')}`]);
  }
  const lines = rows.map(([lhs, rhs]) => `${lhs.padEnd(w)}  ${rhs}`);
  const mul = graph.nodes.filter(n => n.kind === 'mul').length;
  const add = graph.nodes.filter(n => n.kind === 'add').length;
  lines.push(`# ${graph.nodes.length} nodes, ${graph.edges.length} edges, ${mul} × nodes, ${add} + nodes`);
  return lines.join('\n');
}
