// Computational-graph IR for evaluation chains.
//
// Two builders produce the same plain-JSON IR (structured-clone safe, so the
// worker can post it to the UI thread):
//   buildGraphFromAffineChain(chain, F, opts)  — our PolynomialChain (AffineForm gates)
//   buildGraphFromLines(lines, opts)           — line-based chains ({lhs, rhs, mul})
//
// IR schema:
//   { nodes: [{ id, kind, label, wire?, group? }], edges: [{ from, to, label?, neg? }] }
//   kind ∈ 'x' | 'const' | 'add' | 'mul' | 'out' | 'wire'
//     x     — the input variable (id 'x')
//     const — a constant; label is its display string (one node per use)
//     add   — a '+' node: sums its in-edges (edge.neg ⇒ subtracted,
//             edge.label 'k×' ⇒ integer multiple k·w)
//     mul   — a '*' node (exactly two in-edges: a field multiplication)
//     out   — the output node 'P' (exactly one in-edge)
//     wire  — a named alias (a line `w = atom` with no arithmetic)
//   wire   — the wire name defined by this node (mul/add/wire nodes that
//            correspond to a named line); absent on anonymous sub-expressions
//   group  — optional gadget/group tag (passed through from opts.groups)
//   Edges are listed in evaluation order; nodes are listed in topological
//   order (every edge goes from an earlier node to a later one), so
//   "defined before use" is a structural invariant of the builders.
import { parseRhs } from './cgen.js';

class Builder {
  constructor() {
    this.nodes = []; this.edges = [];
    this.byId = new Map(); this.anon = 0;
  }
  node(kind, label, extra = {}) {
    let id = extra.id ?? `n${this.anon++}`;
    if (this.byId.has(id)) { // wire names are unique per chain; anonymous ids never collide
      let j = 2; while (this.byId.has(`${id}#${j}`)) j++; id = `${id}#${j}`;
    }
    const n = { id, kind, label };
    if (extra.wire !== undefined) n.wire = extra.wire;
    if (extra.group !== undefined) n.group = extra.group;
    this.nodes.push(n); this.byId.set(id, n);
    return id;
  }
  edge(from, to, { label, neg } = {}) {
    if (!this.byId.has(from) || !this.byId.has(to)) throw new Error(`graph: edge on unknown node ${from} -> ${to}`);
    const e = { from, to };
    if (label) e.label = label;
    if (neg) e.neg = true;
    this.edges.push(e);
    return e;
  }
  const(label, group) { return this.node('const', String(label), { group }); }
  finish() { return { nodes: this.nodes, edges: this.edges }; }
}

const entries = t => (t instanceof Map ? [...t.entries()] : Object.entries(t).map(([a, b]) => [Number(a), b]));

/** Edge decoration for an integer multiple k·w: label 'k×' when |k|≠1, neg flag when k<0. */
function multipleEdge(k) {
  const a = Math.abs(k);
  const d = {};
  if (a !== 1) d.label = `${a}×`;
  if (k < 0) d.neg = true;
  return d;
}

/**
 * Build the IR of a char-0 PolynomialChain
 *   chain = { wire_names: ['1','x',...], gates: [{left, right, out_wire}], output }
 *   AffineForm = { const, terms: Map<wireIndex, int> }
 * F is a display field: { isZero(c), toDisplay(c) } (e.g. QDisplay / FpDisplay).
 * opts.names   — optional wire-name array overriding chain.wire_names (index = wire)
 * opts.groups  — optional {wireIndex: groupLabel} (or Map) tagging gate outputs by gadget
 * opts.scaleBy — optional field element: appends the leading-coefficient
 *                multiplication P = scaleBy * P̃ (one extra '*' node)
 * opts.outName — output node label (default 'P')
 */
export function buildGraphFromAffineChain(chain, F, { names = null, groups = null, scaleBy = null, outName = 'P' } = {}) {
  const wn = names ?? (chain.wire_names?.length ? chain.wire_names : null);
  const nameOf = w => (wn && wn[w] !== undefined ? wn[w] : (w === 1 ? 'x' : w === 0 ? '1' : `y${w - 2}`));
  const groupOf = w => (groups == null ? undefined : (groups instanceof Map ? groups.get(w) : groups[w]));
  const B = new Builder();
  const wireNode = new Map();               // wire index -> node id
  wireNode.set(1, B.node('x', 'x', { id: 'x' }));

  // node id computing an affine form (creates const / add nodes as needed)
  const formNode = (form, group) => {
    const terms = entries(form.terms).filter(([, k]) => k !== 0).sort((a, b) => a[0] - b[0]);
    const hasConst = !F.isZero(form.const);
    if (terms.length === 1 && !hasConst && terms[0][1] === 1 && terms[0][0] !== 0)
      return wireNode.get(terms[0][0]);
    if (terms.length === 0) return B.const(hasConst ? F.toDisplay(form.const) : '0', group);
    const ins = [];                         // inputs first: nodes stay in topological order
    for (const [w, k] of terms) {
      const src = w === 0 ? B.const('1', group) : wireNode.get(w);
      if (src === undefined) throw new Error(`graph: wire ${w} used before definition`);
      ins.push([src, multipleEdge(k)]);
    }
    if (hasConst) ins.push([B.const(F.toDisplay(form.const), group), {}]);
    const add = B.node('add', '+', { group });
    for (const [src, d] of ins) B.edge(src, add, d);
    return add;
  };

  for (const g of chain.gates) {
    const group = groupOf(g.out_wire);
    const l = formNode(g.left, group), r = formNode(g.right, group);
    const nm = nameOf(g.out_wire);
    const id = B.node('mul', '*', { id: nm, wire: nm, group });
    B.edge(l, id); B.edge(r, id);
    wireNode.set(g.out_wire, id);
  }
  let res = formNode(chain.output);
  if (scaleBy !== null && scaleBy !== undefined) {
    const tilde = outName + '̃';
    // materialize the unscaled result as a named wire when it is a bare sum
    const resNode = B.byId.get(res);
    if (resNode.kind === 'add' && resNode.wire === undefined) resNode.wire = tilde;
    const c = B.const(F.toDisplay(scaleBy));
    const m = B.node('mul', '*', { id: 'scale', wire: outName });
    B.edge(c, m); B.edge(res, m);
    res = m;
  }
  const out = B.node('out', outName, { id: 'out' });
  B.edge(res, out);
  return B.finish();
}

// token classification for line-based chains
const NUM_RE = /^-?(0x[0-9a-fA-F]+|\d+(\.\d+)?([eE][+-]?\d+)?(\/\d+)?)$/;
const MULT_RE = /^(-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)·(.+)$/; // displayed scalar/radix multiple k·w

/**
 * Build the IR of a line-based chain: lines = [{lhs, rhs, mul?}] (the format
 * produced by chain.js renderers and the comparison methods).  Each rhs is
 * parsed with cgen.parseRhs: sums of products of atoms.  Products become
 * '*' nodes (k-ary products are split into k−1 binary '*' nodes, so
 * #mul nodes == multiplication count), sums become '+' nodes (subtraction ⇒
 * edge.neg).  The last line defines the output node (label = its lhs).
 * Atoms: 'x', a previously defined wire, a numeric literal, 'k·w' (integer
 * multiple of a wire), '-w' (negated wire); anything else is a constant.
 * opts.groups — optional {wireName: groupLabel} (or Map).
 */
export function buildGraphFromLines(lines, { groups = null } = {}) {
  const B = new Builder();
  const wires = new Map();
  wires.set('x', B.node('x', 'x', { id: 'x' }));
  const groupOf = w => (groups == null ? undefined : (groups instanceof Map ? groups.get(w) : groups[w]));

  // returns { id, neg } — the node computing the atom and whether it is negated
  const atom = (tok, group) => {
    if (wires.has(tok)) return { id: wires.get(tok), neg: false };
    if (NUM_RE.test(tok)) return { id: B.const(tok, group), neg: false };
    const m = MULT_RE.exec(tok);
    if (m && wires.has(m[2])) return { id: wires.get(m[2]), neg: false, mult: Number(m[1]) };
    if (tok.startsWith('-') && wires.has(tok.slice(1))) return { id: wires.get(tok.slice(1)), neg: true };
    if (tok.startsWith('−') && wires.has(tok.slice(1))) return { id: wires.get(tok.slice(1)), neg: true };
    if (/^[A-Za-z_][\w̃]*$/.test(tok)) throw new Error(`graph: wire '${tok}' used before definition`);
    return { id: B.const(tok, group), neg: false };      // opaque constant (fraction, complex, …)
  };

  // node for a parse-tree node; `named` = wire name to attach when a node is created here
  const build = (node, group, named) => {
    if (node.tok !== undefined) {
      const a = atom(node.tok, group);
      if (a.mult !== undefined || a.neg) {
        // a bare k·w / −w atom on its own: materialize as a '+' node with one decorated edge
        const add = B.node('add', '+', { id: named, wire: named, group });
        B.edge(a.id, add, a.mult !== undefined ? multipleEdge(a.mult) : { neg: true });
        return add;
      }
      if (named !== undefined) {              // alias line: w = atom
        const w = B.node('wire', named, { id: named, wire: named, group });
        B.edge(a.id, w);
        return w;
      }
      return a.id;
    }
    if (node.sum.length === 1 && !node.sum[0].neg) return buildTerm(node.sum[0].t, group, named);
    const ins = [];                         // inputs first: nodes stay in topological order
    for (const { neg, t } of node.sum) {
      // a term that is a single (possibly decorated) atom keeps its decoration on the edge
      if (t.length === 1 && t[0].tok !== undefined) {
        const a = atom(t[0].tok, group);
        const d = a.mult !== undefined ? multipleEdge(a.mult) : {};
        if (neg !== !!a.neg) d.neg = true;
        ins.push([a.id, d]);
      } else {
        ins.push([buildTerm(t, group), neg ? { neg: true } : {}]);
      }
    }
    const add = B.node('add', '+', { id: named, wire: named, group });
    for (const [src, d] of ins) B.edge(src, add, d);
    return add;
  };
  const buildTerm = (factors, group, named) => {
    let acc = null, accNeg = false;
    for (let i = 0; i < factors.length; i++) {
      const f = factors[i];
      const last = i === factors.length - 1;
      let id, neg = false;
      if (f.tok !== undefined) {
        const a = atom(f.tok, group);
        if (a.mult !== undefined) {           // k·w inside a product: an explicit '+' node
          const add = B.node('add', '+', { group });
          B.edge(a.id, add, multipleEdge(a.mult));
          id = add;
        } else { id = a.id; neg = !!a.neg; }
      } else id = build(f, group);
      if (acc === null) { acc = id; accNeg = neg; continue; }
      const m = B.node('mul', '*', last && named !== undefined ? { id: named, wire: named, group } : { group });
      B.edge(acc, m, accNeg ? { neg: true } : {});
      B.edge(id, m, neg ? { neg: true } : {});
      acc = m; accNeg = false;
    }
    if (accNeg) {                             // single negated factor
      const add = B.node('add', '+', { id: named, wire: named, group });
      B.edge(acc, add, { neg: true });
      return add;
    }
    if (factors.length === 1 && named !== undefined && B.byId.get(acc)?.wire !== named) {
      const n = B.byId.get(acc);
      if ((n.kind === 'add' || n.kind === 'mul') && n.wire === undefined) { n.wire = named; return acc; }
      const w = B.node('wire', named, { id: named, wire: named, group });
      B.edge(acc, w);
      return w;
    }
    return acc;
  };

  for (let i = 0; i < lines.length; i++) {
    const { lhs, rhs } = lines[i];
    const group = groupOf(lhs);
    const tree = parseRhs(rhs);
    if (i === lines.length - 1) {
      const res = build(tree, group);
      const out = B.node('out', lhs, { id: 'out', wire: lhs });
      B.edge(res, out);
    } else {
      const id = build(tree, group, lhs);
      wires.set(lhs, id);
    }
  }
  return B.finish();
}

/** Counts: { mul, add, const, nodes, edges }. */
export function graphStats(graph) {
  const c = { mul: 0, add: 0, const: 0, nodes: graph.nodes.length, edges: graph.edges.length };
  for (const n of graph.nodes) if (n.kind in c) c[n.kind]++;
  return c;
}
