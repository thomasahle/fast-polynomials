// runtime.frag.js — shared runtime for the char-0 lane port of
// tools/poly_schedule.py + tools/polychain.py.
// Fragment: declarations only (classes / functions / const). No imports, no
// top-level side effects. Assembled into core.js whose header provides
//   import { Rat } from '../rat.js';
// Field elements are OPAQUE: Rat over Q (modulus === null), BigInt over GF(p)
// (modulus === BigInt prime). NEVER use +,-,* on them directly.

// py: tools/poly_schedule.py:62  (module-level flag; peeled mode is compiled
// out of this port — set_peeled_q flips it exactly like the Python global)
let PEELED_Q = false;

// py: tools/poly_schedule.py:65
function set_peeled_q(flag) {
  PEELED_Q = !!flag;
}

// JS-only helper: BigInt modular exponentiation (Python's pow(a, e, p)).
function _bigint_modpow(base, exp, mod) {
  base %= mod;
  if (base < 0n) base += mod;
  let result = 1n;
  let e = exp;
  while (e > 0n) {
    if (e & 1n) result = (result * base) % mod;
    base = (base * base) % mod;
    e >>= 1n;
  }
  return result;
}

// py: tools/poly_schedule.py:69
// Minimal field-like wrapper for exact rationals or prime fields.
// modulus: null (exact rationals over Rat) or a BigInt prime p (elements are
// canonical BigInt in [0, p)).  `use_fractions` is kept for API parity; the
// only supported modes are (null, true) and (p, false-ish).
class Field {
  constructor({ modulus = null } = {}) {
    if (modulus !== null && typeof modulus !== 'bigint') {
      throw new Error('Field modulus must be null or a BigInt prime');
    }
    this.modulus = modulus;
    this.use_fractions = modulus === null;
  }

  // py: tools/poly_schedule.py:76
  // Accepts: an element of this field, a JS integer Number, or a BigInt.
  // (Over GF(p) an integral Rat is also accepted, mirroring int(x).)
  coerce(x) {
    if (this.modulus !== null) {
      let v;
      if (typeof x === 'bigint') v = x;
      else if (typeof x === 'number' && Number.isInteger(x)) v = BigInt(x);
      else if (x instanceof Rat && x.d === 1n) v = x.n;
      else throw new Error(`cannot coerce ${x} into GF(p)`);
      v %= this.modulus;
      if (v < 0n) v += this.modulus;
      return v;
    }
    return Rat.of(x);
  }

  // JS-only alias used by translated code for integer literals entering
  // field arithmetic (the conventions' field.from_int(k)).
  from_int(k) {
    return this.coerce(k);
  }

  // py: tools/poly_schedule.py:83
  zero() {
    return this.coerce(0);
  }

  // py: tools/poly_schedule.py:86
  one() {
    return this.coerce(1);
  }

  // py: tools/poly_schedule.py:89
  add(a, b) {
    // Coerce both operands: Python mixes plain ints with field elements
    // freely (e.g. AffineForm constants start as int 0); JS must coerce.
    a = this.coerce(a); b = this.coerce(b);
    if (this.modulus !== null) {
      const v = (a + b) % this.modulus;
      return v < 0n ? v + this.modulus : v;
    }
    return a.add(b);
  }

  // py: tools/poly_schedule.py:94
  sub(a, b) {
    a = this.coerce(a); b = this.coerce(b);
    if (this.modulus !== null) {
      const v = (a - b) % this.modulus;
      return v < 0n ? v + this.modulus : v;
    }
    return a.sub(b);
  }

  // py: tools/poly_schedule.py:99
  neg(a) {
    a = this.coerce(a);
    if (this.modulus !== null) {
      const v = (-a) % this.modulus;
      return v < 0n ? v + this.modulus : v;
    }
    return a.neg();
  }

  // py: tools/poly_schedule.py:104
  mul(a, b) {
    a = this.coerce(a); b = this.coerce(b);
    if (this.modulus !== null) {
      const v = (a * b) % this.modulus;
      return v < 0n ? v + this.modulus : v;
    }
    return a.mul(b);
  }

  // py: tools/poly_schedule.py:109
  inv(a) {
    a = this.coerce(a);
    if (this.modulus !== null) {
      const p = this.modulus;
      let v = a % p;
      if (v < 0n) v += p;
      if (v === 0n) throw new Error('division by zero in prime field');
      return _bigint_modpow(v, p - 2n, p);
    }
    if (a.isZero()) throw new Error('division by zero');
    return a.inv();
  }

  // py: tools/poly_schedule.py:120
  div(a, b) {
    return this.mul(a, this.inv(b));
  }

  // py: tools/poly_schedule.py:138
  is_zero(a) {
    a = this.coerce(a);
    if (this.modulus !== null) {
      return a % this.modulus === 0n;
    }
    return a.isZero();
  }

  // JS-only: element equality (Python compares with `==`; JS cannot).
  eq(a, b) {
    a = this.coerce(a); b = this.coerce(b);
    if (this.modulus !== null) return a === b;
    return a.eq(b);
  }
}

// py: tools/poly_schedule.py:145
// Affine form in previously-computed wires:
//     const + sum_{w in terms} (k_w * wire[w])   where k_w is an integer.
// Restriction: wire coefficients are ORDINARY JS integers (Number), never
// field elements — this is the paper's cost model, enforced by validate().
// terms is a Map<number, number> (wire index -> integer coefficient).
// Instances are immutable by convention (Python uses a frozen dataclass):
// never mutate `af.const` or `af.terms` after construction.
class AffineForm {
  constructor(constant, terms) {
    this.const = constant;
    this.terms = terms; // Map<number, number>
  }

  // py: tools/poly_schedule.py:162
  static const_only(c) {
    return new AffineForm(c, new Map());
  }

  // py: tools/poly_schedule.py:166
  static wire(w, coef = 1) {
    if (!Number.isInteger(coef)) throw new Error('wire coefficient must be an int');
    if (coef === 0) return new AffineForm(0, new Map());
    return new AffineForm(0, new Map([[w, coef]]));
  }

  // py: tools/poly_schedule.py:174
  static sum_wires(wires, constant = 0) {
    const terms = new Map();
    for (const w of wires) {
      terms.set(w, (terms.get(w) || 0) + 1);
      if (terms.get(w) === 0) terms.delete(w);
    }
    return new AffineForm(constant, terms);
  }

  // py: tools/poly_schedule.py:183
  add_const(c, field) {
    return new AffineForm(field.add(this.const, c), new Map(this.terms));
  }

  // py: tools/poly_schedule.py:186
  add(other, field) {
    const constant = field.add(this.const, other.const);
    const terms = new Map(this.terms);
    for (const [w, k] of other.terms) {
      terms.set(w, (terms.get(w) || 0) + k);
      if (terms.get(w) === 0) terms.delete(w);
    }
    return new AffineForm(constant, terms);
  }

  // py: tools/poly_schedule.py:195
  sub(other, field) {
    const constant = field.sub(this.const, other.const);
    const terms = new Map(this.terms);
    for (const [w, k] of other.terms) {
      terms.set(w, (terms.get(w) || 0) - k);
      if (terms.get(w) === 0) terms.delete(w);
    }
    return new AffineForm(constant, terms);
  }

  // py: tools/poly_schedule.py:204
  eval(wires, field) {
    let acc = field.coerce(this.const);
    for (let [w, k] of this.terms) {
      if (!Number.isInteger(k)) throw new Error(`wire coefficient must be int, got ${typeof k}`);
      if (k === 0) continue;
      let v = wires[w];
      if (k < 0) {
        v = field.neg(v);
        k = -k;
      }
      // Multiply by a small integer using additions (no field multiplication).
      // Use double-and-add to keep this O(log k) additions.
      let addend = v;
      while (k) {
        if (k & 1) acc = field.add(acc, addend);
        k >>>= 1;
        if (k) addend = field.add(addend, addend);
      }
    }
    return acc;
  }
}

// py: tools/poly_schedule.py:229
class MulGate {
  constructor(left, right, out_wire, label = null) {
    this.left = left;
    this.right = right;
    this.out_wire = out_wire;
    // Provenance (JS-only, display aid): innermost gadget label active when
    // the gate was emitted, e.g. 'Q_7 known-power block'; null if unlabeled.
    this.label = label;
  }
}

// py: tools/poly_schedule.py:236
// A straight-line program:
// - wire 0 is constant 1
// - wire 1 is x
// - each gate appends one wire (a multiplication)
// - output is an AffineForm in the wires
class PolynomialChain {
  constructor(wire_names, gates, output, field, gate_labels = null, gate_label_paths = null) {
    this.wire_names = wire_names;
    this.gates = gates;
    this.output = output;
    this.field = field;
    // JS-only provenance, parallel to `gates`: gate_labels[i] is the innermost
    // gadget label of gate i (or null); gate_label_paths[i] is the full label
    // stack (outermost first) at emission time.  Not part of the Python port.
    this.gate_labels = gate_labels ?? gates.map((g) => g.label ?? null);
    this.gate_label_paths = gate_label_paths ?? gates.map((g) => (g.label_path ?? []).slice());
  }

  // py: tools/poly_schedule.py:250
  eval(x) {
    const wires = [this.field.one(), this.field.coerce(x)];
    for (const gate of this.gates) {
      const left_val = gate.left.eval(wires, this.field);
      const right_val = gate.right.eval(wires, this.field);
      wires.push(this.field.mul(left_val, right_val));
    }
    return this.output.eval(wires, this.field);
  }

  // py: tools/poly_schedule.py:258
  validate() {
    if (this.wire_names.length !== 2 + this.gates.length) {
      throw new Error(
        `wire_names length mismatch: ${this.wire_names.length} != 2 + ${this.gates.length}`
      );
    }

    for (let i = 0; i < this.gates.length; i++) {
      const gate = this.gates[i];
      // Before gate i, wires are [0..(2+i-1)] == [0..(1+i)].
      const max_in_wire = 1 + i;
      for (const [side_name, lf] of [['left', gate.left], ['right', gate.right]]) {
        for (const [w, k] of lf.terms) {
          if (w > max_in_wire) {
            throw new Error(
              `gate ${i} ${side_name} references future wire ${w} (max allowed ${max_in_wire})`
            );
          }
          if (!Number.isInteger(k)) {
            throw new Error(
              `gate ${i} ${side_name} wire ${w} coefficient must be int, got ${typeof k}`
            );
          }
        }
      }
    }

    const max_out_wire = 1 + this.gates.length;
    for (const [w, k] of this.output.terms) {
      if (w > max_out_wire) {
        throw new Error(`output references future wire ${w} (max allowed ${max_out_wire})`);
      }
      if (!Number.isInteger(k)) {
        throw new Error(`output wire ${w} coefficient must be int, got ${typeof k}`);
      }
    }
  }

  // py: tools/poly_schedule.py:289
  // Return [c_list, b_list, out] in the "c_i / b_i" style; every entry is a
  // dense vector of FIELD elements (integer wire coefficients are coerced).
  as_dense_schedule() {
    const field = this.field;

    // py: tools/poly_schedule.py:303
    const dense = (lf, length) => {
      const vec = [];
      for (let j = 0; j < length; j++) vec.push(field.zero());
      vec[0] = field.coerce(lf.const);
      for (const [w, k] of lf.terms) {
        if (w >= length) {
          throw new Error(`affine form references future wire ${w} (len=${length})`);
        }
        if (!Number.isInteger(k)) {
          throw new Error(`wire coefficient must be int, got ${typeof k}`);
        }
        vec[w] = field.coerce(k);
      }
      return vec;
    };

    const c_list = [];
    const b_list = [];
    for (let i = 0; i < this.gates.length; i++) {
      const g = this.gates[i];
      const n_wires_in = 2 + i;
      c_list.push(dense(g.left, n_wires_in));
      b_list.push(dense(g.right, n_wires_in));
    }

    const out = dense(this.output, 2 + this.gates.length);
    return [c_list, b_list, out];
  }

  // py: tools/poly_schedule.py:375
  get mul_count() {
    return this.gates.length;
  }
}

// py: tools/poly_schedule.py:380
// Helper for incrementally building a PolynomialChain.
class ChainBuilder {
  constructor(field) {
    this.field = field;
    this.wire_names = ['1', 'x'];
    this.gates = [];
    // Gadget output values registered as let-bound ("materialized") sums,
    // for share-aware addition counting (the paper's ledger convention:
    // a let-bound subexpression used more than once is charged once).
    this.marked_values = [];
    // JS-only provenance: stack of gadget labels (see pushLabel/popLabel);
    // every gate emitted while a label is active records it (MulGate.label,
    // PolynomialChain.gate_labels).  Purely a display aid — never affects
    // the emitted gates.
    this.label_stack = [];
  }

  // JS-only. Enter a gadget scope: gates emitted until the matching popLabel
  // are attributed to `label` (innermost wins for nested gadgets).
  pushLabel(label) {
    this.label_stack.push(String(label));
  }

  // JS-only. Leave the innermost gadget scope.
  popLabel() {
    this.label_stack.pop();
  }

  // JS-only. Run `fn()` inside a gadget scope (pops even if `fn` throws).
  withLabel(label, fn) {
    this.pushLabel(label);
    try {
      return fn();
    } finally {
      this.popLabel();
    }
  }

  // JS-only. Innermost active label, or null.
  get current_label() {
    return this.label_stack.length ? this.label_stack[this.label_stack.length - 1] : null;
  }

  // py: tools/poly_schedule.py:392
  mark_value(form) {
    this.marked_values.push(form);
    return form;
  }

  // py: tools/poly_schedule.py:396
  get x() {
    return AffineForm.wire(1);
  }

  // py: tools/poly_schedule.py:400
  wire(w, coef = 1) {
    return AffineForm.wire(w, coef);
  }

  // py: tools/poly_schedule.py:403
  const(c) {
    return AffineForm.const_only(this.field.coerce(c));
  }

  // py: tools/poly_schedule.py:406
  add_gate(left, right, name = null) {
    const out_wire = this.wire_names.length;
    const gate = new MulGate(left, right, out_wire, this.current_label);
    gate.label_path = this.label_stack.slice();
    this.gates.push(gate);
    this.wire_names.push(name !== null ? name : `y${out_wire - 2}`);
    return out_wire;
  }

  // py: tools/poly_schedule.py:412
  mul(left, right, name = null) {
    return AffineForm.wire(this.add_gate(left, right, name));
  }

  // py: tools/poly_schedule.py:415
  finalize(output) {
    return new PolynomialChain(
      this.wire_names.slice(),
      this.gates.slice(),
      output,
      this.field,
      this.gates.map((g) => g.label ?? null),
      this.gates.map((g) => (g.label_path ?? []).slice())
    );
  }
}

// py: tools/poly_schedule.py:548
// Multiply a field element by an integer using additions (no field-mul).
function _field_mul_int(field, value, k) {
  if (k === 0) return field.zero();
  if (k < 0) return field.neg(_field_mul_int(field, value, -k));

  let acc = field.zero();
  let addend = field.coerce(value);
  let kk = k;
  while (kk) {
    if (kk & 1) acc = field.add(acc, addend);
    kk >>>= 1;
    if (kk) addend = field.add(addend, addend);
  }
  return acc;
}

// py: tools/poly_schedule.py:568
function _affine_scale_int(field, lf, k) {
  if (k === 0) return AffineForm.const_only(field.zero());
  const constant = _field_mul_int(field, lf.const, k);
  const terms = new Map();
  for (const [w, c] of lf.terms) {
    const cc = c * k;
    if (cc !== 0) terms.set(w, cc);
  }
  return new AffineForm(constant, terms);
}

// =============================================================================
// Coefficient-level polynomial helpers (used for coefficient -> alpha decoding)
// Polynomials are plain JS arrays of field elements, ascending by degree.
// =============================================================================

// py: tools/poly_schedule.py:2107
function _poly_trim(p, field) {
  if (!p || p.length === 0) return [field.zero()];
  const out = p.map((c) => field.coerce(c));
  while (out.length > 1 && field.is_zero(out[out.length - 1])) out.pop();
  return out;
}

// py: tools/poly_schedule.py:2116
function _poly_degree(p) {
  return p.length - 1;
}

// py: tools/poly_schedule.py:2120
function _poly_coeff(p, i, field) {
  if (i < 0) return field.zero();
  return i < p.length ? p[i] : field.zero();
}

// JS-only helper: polynomial equality after trim (Python compares lists with
// `==`; translators must call this instead).
function _poly_eq(p, q, field) {
  const a = _poly_trim(p, field);
  const b = _poly_trim(q, field);
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) {
    if (!field.eq(a[i], b[i])) return false;
  }
  return true;
}

// JS-only helper: `p == [field.zero()]` after trim (the zero polynomial).
function _poly_is_zero(p, field) {
  return p.length === 1 && field.is_zero(p[0]);
}

// py: tools/poly_schedule.py:2126
function _poly_add(p, q, field) {
  const n = Math.max(p.length, q.length);
  const out = [];
  for (let i = 0; i < n; i++) {
    out.push(field.add(_poly_coeff(p, i, field), _poly_coeff(q, i, field)));
  }
  return _poly_trim(out, field);
}

// py: tools/poly_schedule.py:2134
function _poly_sub(p, q, field) {
  const n = Math.max(p.length, q.length);
  const out = [];
  for (let i = 0; i < n; i++) {
    out.push(field.sub(_poly_coeff(p, i, field), _poly_coeff(q, i, field)));
  }
  return _poly_trim(out, field);
}

// py: tools/poly_schedule.py:2142
function _poly_add_const(p, c, field) {
  let out = p.slice();
  if (out.length === 0) out = [field.zero()];
  out[0] = field.add(field.coerce(out[0]), field.coerce(c));
  return _poly_trim(out, field);
}

// py: tools/poly_schedule.py:2150
function _poly_shift_xk(p, k, field) {
  if (k < 0) throw new Error('shift must be >= 0');
  if (k === 0) return p.slice();
  const out = [];
  for (let i = 0; i < k; i++) out.push(field.zero());
  return out.concat(p);
}

// py: tools/poly_schedule.py:2158
function _poly_mul(p, q, field) {
  p = _poly_trim(p, field);
  q = _poly_trim(q, field);
  if (_poly_is_zero(p, field) || _poly_is_zero(q, field)) return [field.zero()];
  const out = [];
  for (let i = 0; i < p.length + q.length - 1; i++) out.push(field.zero());
  for (let i = 0; i < p.length; i++) {
    const a = p[i];
    if (field.is_zero(a)) continue;
    for (let j = 0; j < q.length; j++) {
      const b = q[j];
      if (field.is_zero(b)) continue;
      out[i + j] = field.add(out[i + j], field.mul(a, b));
    }
  }
  return _poly_trim(out, field);
}

// py: tools/poly_schedule.py:2201
function _poly_square(p, field) {
  p = _poly_trim(p, field);
  if (_poly_is_zero(p, field)) return [field.zero()];
  const n = p.length;
  const out = [];
  for (let i = 0; i < 2 * n - 1; i++) out.push(field.zero());
  for (let i = 0; i < n; i++) {
    const a = p[i];
    if (field.is_zero(a)) continue;
    // Diagonal term.
    out[2 * i] = field.add(out[2 * i], field.mul(a, a));
    // Off-diagonal terms counted twice.
    for (let j = i + 1; j < n; j++) {
      const b = p[j];
      if (field.is_zero(b)) continue;
      const prod = field.mul(a, b);
      const prod2 = field.add(prod, prod);
      out[i + j] = field.add(out[i + j], prod2);
    }
  }
  return _poly_trim(out, field);
}

// py: tools/poly_schedule.py:2224
// Polynomial long division by a monic divisor (Lemma `lem:monic-division`).
// Returns [quotient, remainder] with:
//   dividend = quotient*divisor + remainder,  deg(remainder) < deg(divisor).
function _poly_divmod_monic(dividend, divisor, field) {
  dividend = _poly_trim(dividend, field);
  divisor = _poly_trim(divisor, field);
  const deg_divisor = _poly_degree(divisor);
  if (deg_divisor < 1) throw new Error('divisor degree must be >= 1');
  if (!field.eq(_poly_coeff(divisor, deg_divisor, field), field.one())) {
    throw new Error('divisor must be monic');
  }

  const deg_dividend = _poly_degree(dividend);
  if (deg_dividend < deg_divisor) {
    return [[field.zero()], dividend.slice()];
  }

  let rem = dividend.slice();
  const q_deg = deg_dividend - deg_divisor;
  const quot = [];
  for (let i = 0; i <= q_deg; i++) quot.push(field.zero());

  for (let t = q_deg; t >= 0; t--) {
    const coef = _poly_coeff(rem, deg_divisor + t, field);
    quot[t] = coef;
    if (field.is_zero(coef)) continue;
    // rem -= coef * x^t * divisor
    for (let j = 0; j <= deg_divisor; j++) {
      const idx = j + t;
      rem[idx] = field.sub(rem[idx], field.mul(coef, divisor[j]));
    }
  }

  rem = deg_divisor > 0 ? rem.slice(0, deg_divisor) : [field.zero()];
  return [_poly_trim(quot, field), _poly_trim(rem, field)];
}

// py: tools/poly_schedule.py:2354
function _poly_pow(p, e, field) {
  if (e < 0) throw new Error('exponent must be >= 0');
  if (e === 0) return [field.one()];
  p = _poly_trim(p, field);
  let out = [field.one()];
  let base = p.slice();
  let exp = e;
  while (exp > 0) {
    if (exp & 1) out = _poly_mul(out, base, field);
    exp >>>= 1;
    if (exp) base = _poly_square(base, field);
  }
  return _poly_trim(out, field);
}

// py: tools/poly_schedule.py:2372
// Multiply a polynomial by an integer scalar k, interpreted in `field`.
function _poly_scale_int(p, k, field) {
  if (k === 0) return [field.zero()];
  if (k === 1) return _poly_trim(p, field);
  if (k === -1) return _poly_trim(p.map((c) => field.neg(field.coerce(c))), field);
  const kk = field.coerce(k);
  return _poly_trim(p.map((c) => field.mul(field.coerce(c), kk)), field);
}

// py: tools/poly_schedule.py:2387
// Multiply a polynomial by a field scalar `lam`.
function _poly_scale_const(p, lam, field) {
  lam = field.coerce(lam);
  if (field.is_zero(lam)) return [field.zero()];
  if (field.eq(lam, field.one())) return _poly_trim(p, field);
  return _poly_trim(p.map((c) => field.mul(field.coerce(c), lam)), field);
}

// py: tools/poly_schedule.py:2399
// Recover monic S of degree `root_deg` from coefficients of S^2 in degrees
// >= root_deg.  Implements the descending-coefficient induction from
// `sections/constructions.tex`, Lemma `lem:monic-from-power` specialized to m=2.
function _monic_sqrt_from_high_square_coeffs(square, root_deg, field) {
  if (root_deg < 1) throw new Error('root_deg must be >= 1');
  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) throw new Error('monic square root requires char(F) != 2');

  square = _poly_trim(square, field);
  if (_poly_degree(square) < 2 * root_deg) {
    throw new Error('square polynomial degree too small for requested root_deg');
  }
  if (!field.eq(square[2 * root_deg], field.one())) {
    throw new Error('square polynomial must be monic at degree 2*root_deg');
  }

  const inv2 = field.inv(two);
  const s = [];
  for (let i = 0; i <= root_deg; i++) s.push(field.zero());
  s[root_deg] = field.one();

  // For t=1..root_deg, solve coefficient at x^{2d - t}.
  for (let t = 1; t <= root_deg; t++) {
    const power = 2 * root_deg - t;
    const target = square[power];

    let known = field.zero();
    for (let j = 1; j < t; j++) {
      const a = s[root_deg - j];
      const b = s[root_deg - (t - j)];
      known = field.add(known, field.mul(a, b));
    }

    const s_dt = field.mul(field.sub(target, known), inv2);
    s[root_deg - t] = s_dt;
  }

  return _poly_trim(s, field);
}

// =============================================================================
// Deterministic PRNG (replacement for random.Random in
// _decode_by_descending_pivots).  xorshift64* over BigInt; randrange(lo, hi)
// returns a JS integer Number in [lo, hi).  Exact values need not match
// Python — the pivot routine self-verifies and the decoded parameter map is a
// bijection, so final outputs still match Python exactly.
// =============================================================================
function makeRng(seed) {
  const MASK = (1n << 64n) - 1n;
  let state = (BigInt(seed) & MASK) ^ 0x9e3779b97f4a7c15n;
  if (state === 0n) state = 0x9e3779b97f4a7c15n;
  const next = () => {
    state ^= (state << 13n) & MASK;
    state ^= state >> 7n;
    state ^= (state << 17n) & MASK;
    state &= MASK;
    return (state * 0x2545f4914f6cdd1dn) & MASK;
  };
  return {
    randrange(lo, hi) {
      if (!Number.isInteger(lo) || !Number.isInteger(hi) || hi <= lo) {
        throw new Error(`invalid randrange bounds (${lo}, ${hi})`);
      }
      const span = BigInt(hi - lo);
      return lo + Number(next() % span);
    },
  };
}
