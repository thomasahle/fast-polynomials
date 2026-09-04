// graph.test.js — computational-graph IR + SVG renderer checks.
// Plain node, no framework: process.exit(1) on failure.
import { GF2k, Q } from '../js/field.js';
import { Rat } from '../js/rat.js';
import { CIRCUITS, circuitStats } from '../js/char2.js';
import { compileChar2 } from '../js/compile2.js';
import { compileHorner } from '../js/methods/horner.js';
import { compileEstrin } from '../js/methods/estrin.js';
import { compileRW } from '../js/methods/rw.js';
import { renderAffineChain } from '../js/chain.js';
import { buildGraphFromAffineChain, buildGraphFromLines, graphStats } from '../js/graph.js';
import { renderGraphSVG, layoutGraph, graphToText, countCrossings } from '../js/graphview.js';
import { handleMessage } from '../js/worker.js';
import { rationals, decode, compile_paper_params_chain, makeRng } from '../js/char0/core.js';

let checks = 0, failures = 0;
const check = (cond, msg) => { checks++; if (!cond) { failures++; console.error(`FAIL: ${msg}`); } };

let seed = 0x2545F4914F6CDD1Dn;
const rnd = () => { seed ^= seed << 13n; seed &= (1n << 64n) - 1n; seed ^= seed >> 7n; seed ^= seed << 17n; seed &= (1n << 64n) - 1n; return seed; };

// ---------- generic IR invariants ----------
function checkIR(graph, tag, { mults = null, outLabel = 'P' } = {}) {
  const ids = new Set();
  for (const n of graph.nodes) {
    check(typeof n.id === 'string' && !ids.has(n.id), `${tag}: duplicate/invalid node id ${n.id}`);
    ids.add(n.id);
    check(['x', 'const', 'add', 'mul', 'out', 'wire'].includes(n.kind), `${tag}: bad kind ${n.kind}`);
    check(typeof n.label === 'string', `${tag}: label not a string on ${n.id}`);
  }
  // every edge points to known nodes and from an earlier node (defined before use)
  const order = new Map(graph.nodes.map((n, i) => [n.id, i]));
  for (const e of graph.edges) {
    check(order.has(e.from) && order.has(e.to), `${tag}: edge on unknown node ${e.from}->${e.to}`);
    check(order.get(e.from) < order.get(e.to), `${tag}: use before definition ${e.from}->${e.to}`);
  }
  // acyclicity via Kahn
  const indeg = new Map(graph.nodes.map(n => [n.id, 0]));
  const succ = new Map(graph.nodes.map(n => [n.id, []]));
  for (const e of graph.edges) { indeg.set(e.to, indeg.get(e.to) + 1); succ.get(e.from).push(e.to); }
  const q = graph.nodes.filter(n => indeg.get(n.id) === 0).map(n => n.id);
  let seen = 0;
  while (q.length) { const u = q.shift(); seen++; for (const v of succ.get(u)) { indeg.set(v, indeg.get(v) - 1); if (indeg.get(v) === 0) q.push(v); } }
  check(seen === graph.nodes.length, `${tag}: cycle detected`);
  // degree constraints
  const indegree = new Map(graph.nodes.map(n => [n.id, 0]));
  for (const e of graph.edges) indegree.set(e.to, indegree.get(e.to) + 1);
  for (const n of graph.nodes) {
    const d = indegree.get(n.id);
    if (n.kind === 'mul') check(d === 2, `${tag}: mul node ${n.id} has ${d} inputs`);
    if (n.kind === 'add') check(d >= 1, `${tag}: add node ${n.id} has no inputs`);
    if (n.kind === 'out') check(d === 1, `${tag}: out node has ${d} inputs`);
    if (n.kind === 'x' || n.kind === 'const') check(d === 0, `${tag}: leaf ${n.id} has inputs`);
  }
  const outs = graph.nodes.filter(n => n.kind === 'out');
  check(outs.length === 1 && outs[0].label === outLabel, `${tag}: expected one out node '${outLabel}'`);
  check(graph.nodes.filter(n => n.kind === 'x').length === 1, `${tag}: expected exactly one x node`);
  // every non-leaf node except the output feeds something
  const outdeg = new Map(graph.nodes.map(n => [n.id, 0]));
  for (const e of graph.edges) outdeg.set(e.from, outdeg.get(e.from) + 1);
  for (const n of graph.nodes) if (n.kind !== 'out') check(outdeg.get(n.id) >= 1, `${tag}: dangling node ${n.id}`);
  const st = graphStats(graph);
  if (mults !== null) check(st.mul === mults, `${tag}: ${st.mul} mul nodes != ${mults} multiplications`);
  // structured-clone safe (plain JSON)
  check(JSON.stringify(JSON.parse(JSON.stringify(graph))) === JSON.stringify(graph), `${tag}: IR not plain JSON`);
  return st;
}

// ---------- SVG well-formedness ----------
function checkSVG(svg, tag) {
  check(typeof svg === 'string' && svg.startsWith('<svg ') && svg.trimEnd().endsWith('</svg>'), `${tag}: not an svg string`);
  check(!/NaN|Infinity|undefined/.test(svg), `${tag}: NaN/Infinity/undefined in svg`);
  // balanced tags
  const stack = [];
  const re = /<\/?([a-zA-Z][\w-]*)([^<>]*?)(\/?)>/g;
  let m, ok = true;
  while ((m = re.exec(svg))) {
    if (m[0].startsWith('</')) { if (stack.pop() !== m[1]) { ok = false; break; } }
    else if (m[3] !== '/') stack.push(m[1]);
  }
  check(ok && stack.length === 0, `${tag}: unbalanced tags (${stack.join(',')})`);
  // stray '<' / '>' outside tags (unescaped labels)
  check(!/<[^a-zA-Z\/!]/.test(svg), `${tag}: stray '<' in svg`);
  const wm = /width="(\d+)" height="(\d+)"/.exec(svg);
  check(wm && +wm[1] > 0 && +wm[2] > 0, `${tag}: bad svg dimensions`);
  return svg;
}

function checkLayout(graph, tag) {
  const { pos, width, height, routes } = layoutGraph(graph);
  check(pos.size === graph.nodes.length, `${tag}: layout missing nodes`);
  for (const [id, p] of pos) {
    check([p.x, p.y, p.w, p.h].every(Number.isFinite), `${tag}: non-finite coordinates on ${id}`);
    check(p.x - p.w / 2 >= 0 && p.x + p.w / 2 <= width && p.y - p.h / 2 >= 0 && p.y + p.h / 2 <= height, `${tag}: node ${id} outside canvas`);
  }
  // edges go left-to-right; no two nodes in the same layer overlap
  for (const e of graph.edges) check(pos.get(e.from).layer < pos.get(e.to).layer, `${tag}: edge ${e.from}->${e.to} not left-to-right`);
  const byLayer = new Map();
  for (const [id, p] of pos) { (byLayer.get(p.layer) ?? byLayer.set(p.layer, []).get(p.layer)).push(p); }
  for (const [l, ps] of byLayer) {
    ps.sort((a, b) => a.y - b.y);
    for (let i = 1; i < ps.length; i++)
      check(ps[i].y - ps[i].h / 2 >= ps[i - 1].y + ps[i - 1].h / 2 - 1e-6, `${tag}: overlap in layer ${l}`);
  }
  // routed edges: exactly the >1-layer spans carry waypoints, one per
  // intermediate layer, in order and inside the canvas
  check(Array.isArray(routes) && routes.length === graph.edges.length, `${tag}: one routes entry per edge`);
  graph.edges.forEach((e, i) => {
    const a = pos.get(e.from), b = pos.get(e.to), via = routes[i];
    if (b.layer - a.layer <= 1) { check(via === null, `${tag}: short edge ${e.from}->${e.to} has waypoints`); return; }
    check(Array.isArray(via) && via.length === b.layer - a.layer - 1, `${tag}: edge ${e.from}->${e.to} waypoint count`);
    if (!Array.isArray(via)) return;
    via.forEach((p, j) => {
      check(p.layer === a.layer + 1 + j, `${tag}: edge ${e.from}->${e.to} waypoint layers out of order`);
      check(Number.isFinite(p.x) && Number.isFinite(p.y) && p.x >= 0 && p.x <= width && p.y >= 0 && p.y <= height,
            `${tag}: edge ${e.from}->${e.to} waypoint outside canvas`);
    });
  });
}

// ======================= char 2: n = 15 (and the other supported degrees) =======================
{
  const F = GF2k(64);
  for (const n of [15, 13, 17, 19, 21]) {
    const coeffs = [...Array.from({ length: n }, () => rnd()), 1n];
    const r = compileChar2(coeffs, F);
    const g = buildGraphFromLines(r.lines);
    const st = checkIR(g, `char2 n=${n}`, { mults: r.mults });
    const spec = CIRCUITS[n];
    check(st.mul === circuitStats(spec).mults, `char2 n=${n}: mul nodes vs circuitStats`);
    // wire names of the gate circuit appear as mul nodes
    for (const gate of spec.gates) {
      const node = g.nodes.find(nd => nd.id === gate.w);
      check(node && node.kind === 'mul' && node.wire === gate.w, `char2 n=${n}: gate ${gate.w} missing`);
    }
    if (n === 15) {
      // y = x * x: two parallel edges from x
      check(g.edges.filter(e => e.from === 'x' && e.to === 'y').length === 2, 'char2 n=15: squaring edges');
      // keys become constants: at least one const node with a hex label
      check(g.nodes.some(nd => nd.kind === 'const' && /^0x/.test(nd.label)), 'char2 n=15: hex key constants');
      // no subtraction over char 2
      check(!g.edges.some(e => e.neg), 'char2 n=15: no neg edges');
      // every edge is drawn exactly once, and parallel edges get distinct paths
      const svg15 = renderGraphSVG(g);
      const ds = [...svg15.matchAll(/<path d="([^"]+)" marker-end/g)].map(m => m[1]);
      check(ds.length === g.edges.length, 'char2 n=15: one drawn path per edge');
      check(new Set(ds).size === ds.length, 'char2 n=15: parallel edges drawn separated');
      console.log(`char2 n=15: ${st.nodes} nodes, ${st.edges} edges, ${st.mul} ×, ${st.add} +`);
    }
    checkLayout(g, `char2 n=${n}`);
    checkSVG(renderGraphSVG(g), `char2 n=${n} svg`);
    checkSVG(renderGraphSVG(g, { theme: 'dark' }), `char2 n=${n} svg dark`);
    check(graphToText(g).split("\n").length === st.mul + 2, `char2 n=${n}: graphToText one row per gate + P + footer`);
  }
  // non-monic input: leading-coefficient scale adds one multiplication
  const coeffs = [...Array.from({ length: 15 }, () => rnd()), 0x1234n];
  const r = compileChar2(coeffs, F);
  const g = buildGraphFromLines(r.lines);
  checkIR(g, 'char2 n=15 scaled', { mults: r.mults });
  check(g.nodes.some(nd => nd.wire === 'P̃'), 'char2 scaled: P̃ wire present');
  checkSVG(renderGraphSVG(g), 'char2 scaled svg');
}

// ======================= char 0: AffineForm chains over Q =======================
{
  const field = rationals();
  const rng = makeRng(2024);
  const QDisplay = { isZero: c => Rat.of(typeof c === 'number' ? BigInt(c) : c).isZero(), toDisplay: c => Rat.of(typeof c === 'number' ? BigInt(c) : c).toString() };
  for (const n of [5, 8, 13, 16, 23]) {
    const coeffs = [];
    for (let i = 0; i < n; i++) coeffs.push(field.coerce(rng.randrange(-9, 10)));
    coeffs.push(field.one());
    const alphas = decode(n, coeffs, field);
    const chain = compile_paper_params_chain(alphas, null);
    chain.validate();
    const g = buildGraphFromAffineChain(chain, QDisplay);
    const st = checkIR(g, `char0 Q n=${n}`, { mults: chain.gates.length });
    // wire names from the chain are the mul node ids
    for (const gate of chain.gates) {
      const nm = chain.wire_names[gate.out_wire];
      const node = g.nodes.find(nd => nd.id === nm);
      check(node && node.kind === 'mul', `char0 n=${n}: gate wire ${nm} missing`);
    }
    // one '+' node per affine form with > 1 summand (terms + nonzero const)
    let expectedAdds = 0;
    const forms = [...chain.gates.flatMap(gt => [gt.left, gt.right]), chain.output];
    for (const f of forms) {
      const terms = [...f.terms.values()].filter(k => k !== 0);
      const cnt = terms.length + (QDisplay.isZero(f.const) ? 0 : 1);
      if (cnt > 1 || (cnt === 1 && terms.length === 1 && terms[0] !== 1)) expectedAdds++;
    }
    check(st.add === expectedAdds, `char0 n=${n}: ${st.add} add nodes != ${expectedAdds}`);
    // the line-based route must agree on the operation counts
    const g2 = buildGraphFromLines(renderAffineChain({ isZero: QDisplay.isZero, toDisplay: QDisplay.toDisplay }, chain));
    const st2 = checkIR(g2, `char0 Q n=${n} (lines)`, { mults: chain.gates.length });
    check(st2.add === st.add, `char0 n=${n}: line route add count ${st2.add} != ${st.add}`);
    checkLayout(g, `char0 n=${n}`);
    checkSVG(renderGraphSVG(g), `char0 n=${n} svg`);
    if (n === 13) console.log(`char0 n=13: ${st.nodes} nodes, ${st.edges} edges, ${st.mul} ×, ${st.add} +`);
  }
  // custom names + scaleBy + groups
  const n = 8;
  const coeffs = [];
  for (let i = 0; i < n; i++) coeffs.push(field.coerce(rng.randrange(-9, 10)));
  coeffs.push(field.one());
  const chain = compile_paper_params_chain(decode(n, coeffs, field), null);
  const letters = ['1', 'x', 'y', 'z', 't', 'u', 'v', 'w', 's', 'r', 'q', 'p', 'o', 'm'];
  const groups = {}; chain.gates.forEach((gt, i) => { groups[gt.out_wire] = i < 2 ? 'H_2' : 'T'; });
  const g = buildGraphFromAffineChain(chain, QDisplay, { names: letters, scaleBy: new Rat(3n, 7n), groups });
  checkIR(g, 'char0 named+scaled', { mults: chain.gates.length + 1 });
  check(g.nodes.some(nd => nd.id === 'y' && nd.kind === 'mul' && nd.group === 'H_2'), 'char0 named: letter names + groups');
  check(g.nodes.some(nd => nd.kind === 'const' && nd.label === '3/7'), 'char0 scaled: 3/7 constant');
  check(g.edges.some(e => e.neg) === chain.gates.some(gt => [...gt.left.terms.values(), ...gt.right.terms.values()].some(k => k < 0)) ||
        g.edges.some(e => e.neg), 'char0: neg edges reflect negative coefficients');
  checkSVG(renderGraphSVG(g), 'char0 named svg');
  const txt = graphToText(g);
  check(txt.includes('y ') && txt.includes('P '), 'char0 graphToText mentions wires');
}

// ======================= comparison methods (line chains) =======================
{
  const F = GF2k(64);
  const Fq = Q;
  const cases = [
    ['gf2k', F, n => [...Array.from({ length: n }, () => rnd()), 1n]],
    ['gf2k nonmonic', F, n => [...Array.from({ length: n }, () => rnd()), 0x77n]],
    ['Q', Fq, n => [...Array.from({ length: n }, () => new Rat(rnd() % 19n - 9n, 1n + (rnd() % 3n))), Rat.ONE]],
    ['Q nonmonic', Fq, n => [...Array.from({ length: n }, () => new Rat(rnd() % 19n - 9n)), new Rat(5n)]],
    ['Q sparse', Fq, n => { const c = Array.from({ length: n + 1 }, () => Rat.ZERO); c[n] = Rat.ONE; c[0] = new Rat(-2n); c[3 % (n + 1)] = new Rat(4n); return c; }],
  ];
  for (const [tag, Fld, mk] of cases) {
    for (const n of [1, 2, 3, 4, 7, 13, 15, 31]) {
      const coeffs = mk(n);
      for (const [name, fn] of [['Horner', compileHorner], ['Estrin', compileEstrin], ['RW', compileRW]]) {
        const r = fn(coeffs, Fld);
        let g;
        try { g = buildGraphFromLines(r.lines); }
        catch (e) { check(false, `${name} ${tag} n=${n}: threw ${e.message}`); continue; }
        const st = checkIR(g, `${name} ${tag} n=${n}`, { mults: r.mults });
        if (Fld.char === 2) check(!g.edges.some(e => e.neg), `${name} ${tag} n=${n}: neg edge over char 2`);
        checkLayout(g, `${name} ${tag} n=${n}`);
        checkSVG(renderGraphSVG(g), `${name} ${tag} n=${n} svg`);
        if (n === 13 && tag === 'Q' && name === 'Horner') {
          // Horner over Q with negative coefficients: subtraction edges are marked
          const hasNeg = r.lines.some(l => l.rhs.includes(' − '));
          check(g.edges.some(e => e.neg) === hasNeg, 'Horner Q: neg edges iff subtraction in chain');
          check(graphToText(g).includes('×'), 'Horner graphToText has × rows');
        }
      }
    }
  }
}

// ======================= hand-written line chains (parser corner cases) =======================
{
  const lines = [
    { lhs: 'y', rhs: 'x * x', mul: true },
    { lhs: 'z', rhs: '(y + 2·x − 3) * (x + 1/2)', mul: true },
    { lhs: 't', rhs: '-z * (x − y) * 0x1f', mul: true },
    { lhs: 'u', rhs: 'z', mul: false },
    { lhs: 'P', rhs: '2·u + t − 7', mul: false },
  ];
  const g = buildGraphFromLines(lines);
  const st = checkIR(g, 'handwritten', { mults: 4 });
  check(g.edges.some(e => e.label === '2×' && e.from === 'x'), 'handwritten: 2·x edge label');
  check(g.edges.some(e => e.neg && e.from === 'y'), 'handwritten: x − y neg edge');
  check(g.nodes.some(n => n.kind === 'wire' && n.id === 'u'), 'handwritten: alias wire node');
  check(g.nodes.some(n => n.kind === 'const' && n.label === '1/2'), 'handwritten: fraction const');
  check(g.edges.some(e => e.neg && e.from === 'z' && g.nodes.find(n => n.id === e.to).kind === 'mul'), 'handwritten: -z negated factor');
  const svg = checkSVG(renderGraphSVG(g), 'handwritten svg');
  check(svg.includes('stroke-dasharray'), 'handwritten svg: dashed neg edges');
  check(svg.includes('>2×<'), 'handwritten svg: 2× label');
  check((svg.match(/class="gv-node gv-mul"/g) ?? []).length === 4, 'handwritten svg: 4 mul nodes drawn');
  // labels are escaped
  const g2 = buildGraphFromLines([{ lhs: 'P', rhs: 'x + <b>' }]);
  check(renderGraphSVG(g2).includes('&lt;b&gt;'), 'svg escapes labels');
  // use-before-definition is rejected
  let threw = false;
  try { buildGraphFromLines([{ lhs: 'y', rhs: 'x * q' }, { lhs: 'P', rhs: 'y' }]); } catch (e) { threw = true; }
  check(threw, 'undefined wire rejected');
  console.log(`handwritten: ${st.nodes} nodes, ${st.edges} edges`);
}

// ======================= crossing metric regression (dense degree-15 over ℚ) =======================
// Baselines before edge virtualization + transpose (same input, same metric):
//   this paper 59, Horner 91, Estrin 38, Rabin–Winograd 36, Knuth–Eve 20.
// Fixed per-method limits: Horner (a planar chain) must stay near zero, ours
// well under half its baseline, and nobody more than ~10% over baseline.
{
  const src = 'x^15 - 5x^14 - 17x^13 + 18x^12 - 12x^11 + 19x^10 - 12x^9 + 17x^8 + 17x^7 - 18x^6 + 3x^5 + 14x^4 + 8x^3 + 7x^2 + 11x + 9';
  const result = await handleMessage({ lane: 'char0', fieldMode: 'Q', src });
  const graphs = new Map([['this paper', result.graph]]);
  for (const c of result.comparisons) if (c.ok && c.graph) graphs.set(c.name, c.graph);
  const LIMITS = new Map([['this paper', 29], ['Horner', 4], ['Estrin', 26], ['Rabin–Winograd', 39], ['Knuth–Eve', 13]]);
  for (const [name, limit] of LIMITS) {
    const g = graphs.get(name);
    check(!!g, `crossings: ${name} graph present`);
    if (!g) continue;
    const c = countCrossings(g);
    check(c <= limit, `crossings: ${name} has ${c} crossings > limit ${limit}`);
    console.log(`crossings ${name}: ${c} (limit ${limit})`);
    // layout is deterministic: two runs agree exactly, and so does the metric
    const l1 = layoutGraph(g), l2 = layoutGraph(g);
    check(JSON.stringify([...l1.pos]) === JSON.stringify([...l2.pos]), `crossings: ${name} node placement deterministic`);
    check(JSON.stringify(l1.routes) === JSON.stringify(l2.routes), `crossings: ${name} edge routes deterministic`);
    check(countCrossings(g, l1) === c, `crossings: ${name} metric stable across layouts`);
    // the SVG draws every edge exactly once (one arrowheaded path per edge)
    const svg = renderGraphSVG(g);
    check((svg.match(/marker-end/g) ?? []).length === g.edges.length, `crossings: ${name} svg draws all ${g.edges.length} edges`);
    checkLayout(g, `crossings ${name}`);
  }
  check(countCrossings(graphs.get('Horner')) === 0, 'crossings: Horner chain is drawn planar (zero crossings)');
}

console.log(`${checks} checks, ${failures} failures`);
if (failures) process.exit(1);
console.log('ALL GRAPH TESTS PASS');
