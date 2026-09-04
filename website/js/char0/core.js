// core.js — characteristic-0 lane of the "Fast Evaluation of Polynomials with
// Rational Preprocessing" reference implementation, ported from
// tools/polychain.py + tools/poly_schedule.py.
// ASSEMBLED FILE: edit the .frag.js fragments and re-assemble; each function
// carries a "// py:" provenance comment pointing at its Python source line.
import { Rat } from '../rat.js';

// ====================================================================
// BEGIN runtime.frag.js
// ====================================================================
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

// ====================================================================
// BEGIN g3_poly_paper.frag.js
// ====================================================================
// g3_poly_paper.frag.js — coefficient-level reference expansions
// (_poly_paper_* twins of the chain emitters) from tools/poly_schedule.py.
// Fragment: function declarations only; no imports/exports, no top-level
// side effects.  Depends on runtime.frag.js (Field, PEELED_Q, _poly_* helpers)
// and on _v2_positive (g1_emit_bases.frag.js).

// py: tools/poly_schedule.py:1826
// Coefficient-level twin of `_paper_QO`.
function _poly_QO({ deg, alpha, Hs, field }) {
  if (deg === 1) {
    return _poly_add_const(Hs[0], field.coerce(alpha[0]), field);
  }
  const t = 32 - Math.clz32(deg); // deg.bit_length()
  if (deg === (1 << t) - 1) {
    return _poly_paper_Q_known_powers({ k: t, alpha: alpha, Hs: Hs.slice(0, t), field: field });
  }
  const h = 1 << (t - 1);
  const w = deg - h;
  const ud = 2 * h - deg;
  const U = _poly_QO({ deg: ud, alpha: alpha.slice(0, ud), Hs: Hs, field: field });
  const W = _poly_QO({ deg: w, alpha: alpha.slice(ud, ud + w), Hs: Hs, field: field });
  const B = _poly_QO({ deg: w, alpha: alpha.slice(ud + w), Hs: Hs, field: field });
  return _poly_add(_poly_mul(_poly_add(Hs[t - 1], U, field), W, field), B, field);
}

// py: tools/poly_schedule.py:3641
// Coefficient-level encoder for:
//   Q_3[α0,α1,α2](x,H2) = (x+α2)(H2+α1) + α0
function _poly_paper_q3({ alpha0, alpha1, alpha2, H2, field }) {
  const x = [field.zero(), field.one()];
  const t1 = _poly_add_const(x, alpha2, field);
  const t2 = _poly_add_const(H2, alpha1, field);
  return _poly_add(_poly_mul(t1, t2, field), [field.coerce(alpha0)], field);
}

// py: tools/poly_schedule.py:3653
// Coefficient-level encoder matching `_paper_A_fill` (Algorithm `alg:constr-fill`).
function _poly_paper_A_fill({ l, alpha, beta, S1_2l, S2_2l, Hs, field }) {
  if (l < 0) throw new Error('A_fill requires l >= 0');
  if (l > 0 && Hs.length <= l) {
    throw new Error(`A_fill requires Hs up to index ${l} (H_{2^${l}})`);
  }

  const need_alpha = (1 << (l + 1)) - 2;
  const need_beta = (1 << l) + 1;
  if (alpha.length !== need_alpha) {
    throw new Error(`A_fill l=${l} needs ${need_alpha} alpha params, got ${alpha.length}`);
  }
  if (beta.length !== need_beta) {
    throw new Error(`A_fill l=${l} needs ${need_beta} beta params, got ${beta.length}`);
  }

  alpha = alpha.map((a) => field.coerce(a));
  beta = beta.map((b) => field.coerce(b));

  const x = Hs[0];

  function A1(l_, S1) {
    if (l_ === 0) {
      return _poly_trim(S1, field);
    }
    if (l_ === 1) {
      // A^{(1)}_2 = (H2 + β1) S1 + α1
      const t = _poly_mul(_poly_add_const(Hs[1], beta[1], field), S1, field);
      return _poly_add_const(t, alpha[1], field);
    }
    if (l_ === 2) {
      // S^{(1)}_2 = (H4 + β3) S^{(1)}_4 + Q_3[α3,α4,α5](x,H2)
      const q3 = _poly_paper_q3({ alpha0: alpha[3], alpha1: alpha[4], alpha2: alpha[5], H2: Hs[1], field: field });
      const t = _poly_mul(_poly_add_const(Hs[2], beta[3], field), S1, field);
      const S1_2 = _poly_add(t, q3, field);
      // A^{(1)}_4 = (H2 + β1) S^{(1)}_2 + α1
      const t2 = _poly_mul(_poly_add_const(Hs[1], beta[1], field), S1_2, field);
      return _poly_add_const(t2, alpha[1], field);
    }

    // l_ >= 3
    const k_small = l_ - 1; // Q_{2^{k_small}-1}
    // Q_{2^{l_-1}-1}[β_{2^{l_}-1}, ..., β_{2^{l_-1}+1}] in descending β-index order.
    const q_small_params = beta.slice((1 << (l_ - 1)) + 1, 1 << l_).reverse();
    const q_small = _poly_paper_Q_known_powers({ k: k_small, alpha: q_small_params, Hs: Hs.slice(0, l_ - 1), field: field });

    const factor = _poly_add(Hs[l_], q_small, field);
    const t = _poly_mul(factor, S1, field);

    const q_big_params = alpha.slice((1 << l_) - 1, (1 << (l_ + 1)) - 2);
    const q_big = _poly_paper_Q_known_powers({ k: l_, alpha: q_big_params, Hs: Hs.slice(0, l_), field: field });
    const S1_prev = _poly_add(t, q_big, field);
    return A1(l_ - 1, S1_prev);
  }

  function A2(l_, S2) {
    if (l_ === 0) {
      return _poly_trim(S2, field);
    }
    if (l_ === 1) {
      // A^{(2)}_2 = (H2 + β2) S2 + α0
      const t = _poly_mul(_poly_add_const(Hs[1], beta[2], field), S2, field);
      return _poly_add_const(t, alpha[0], field);
    }
    if (l_ === 2) {
      // S^{(2)}_2 = (H4 + β4) S^{(2)}_4 + α2
      const t = _poly_mul(_poly_add_const(Hs[2], beta[4], field), S2, field);
      const S2_2 = _poly_add_const(t, alpha[2], field);
      // A^{(2)}_4 = (H2 + β2) S^{(2)}_2 + α0
      const t2 = _poly_mul(_poly_add_const(Hs[1], beta[2], field), S2_2, field);
      return _poly_add_const(t2, alpha[0], field);
    }

    // l_ >= 3
    const t = _poly_mul(_poly_add_const(Hs[l_], beta[1 << l_], field), S2, field);
    const S2_prev = _poly_add_const(t, alpha[(1 << l_) - 2], field);
    return A2(l_ - 1, S2_prev);
  }

  const A1_out = A1(l, S1_2l);
  const A2_out = A2(l, S2_2l);

  if (l === 0) {
    const t = _poly_mul(_poly_add_const(x, beta[0], field), A1_out, field);
    return _poly_add_const(_poly_add(t, A2_out, field), beta[1], field);
  }

  const t = _poly_mul(_poly_add_const(x, beta[0], field), A1_out, field);
  return _poly_add(t, A2_out, field);
}

// py: tools/poly_schedule.py:3745
// Coefficient-level encoder matching `_paper_Q_known_powers`
// (Algorithm `alg:constr-known-2n-1`).
function _poly_paper_Q_known_powers({ k, alpha, Hs, field }) {
  if (k < 0) throw new Error('Q_known_powers requires k >= 0');
  const need = k === 0 ? 1 : (1 << k) - 1;
  if (alpha.length !== need) {
    throw new Error(`Q_known_powers k=${k} needs ${need} alpha params, got ${alpha.length}`);
  }
  if (k >= 1 && Hs.length <= k - 1) {
    throw new Error(`Q_known_powers k=${k} needs Hs up to index ${k - 1} (H_{2^${k - 1}})`);
  }

  alpha = alpha.map((a) => field.coerce(a));

  if (PEELED_Q && k >= 3) {
    const m = (1 << (k - 1)) - 1;
    const gamma = alpha[0];
    const W = _poly_paper_Q_known_powers({ k: k - 1, alpha: alpha.slice(1, 1 + m), Hs: Hs.slice(0, k - 1), field: field });
    const B = _poly_paper_Q_known_powers({ k: k - 1, alpha: alpha.slice(1 + m), Hs: Hs.slice(0, k - 1), field: field });
    const t = _poly_mul(_poly_add_const(Hs[k - 1], gamma, field), W, field);
    return _poly_add(t, B, field);
  }

  const x = Hs[0];
  if (k === 0) {
    return [alpha[0]];
  }
  if (k === 1) {
    return _poly_add_const(x, alpha[0], field);
  }
  if (k === 2) {
    return _poly_paper_q3({ alpha0: alpha[0], alpha1: alpha[1], alpha2: alpha[2], H2: Hs[1], field: field });
  }
  if (k === 3) {
    // Q_7 via A_2 on (H4+α3, H4+α2) with β2=α4, β1=α5, β0=α6.
    const H4 = Hs[2];
    const S1 = _poly_add_const(H4, alpha[3], field);
    const S2 = _poly_add_const(H4, alpha[2], field);
    const a_alpha = [alpha[0], alpha[1]];
    const beta = [field.zero(), field.zero(), field.zero()]; // β0..β2
    beta[2] = alpha[4];
    beta[1] = alpha[5];
    beta[0] = alpha[6];
    return _poly_paper_A_fill({ l: 1, alpha: a_alpha, beta: beta, S1_2l: S1, S2_2l: S2, Hs: Hs.slice(0, 2), field: field });
  }

  // k >= 4
  const sub_k = k - 2;
  const sub_start = (1 << (k - 1)) - 1;
  const sub_end = (1 << (k - 1)) + (1 << (k - 2)) - 2;
  const q_sub_params = alpha.slice(sub_start, sub_end);
  const q_sub = _poly_paper_Q_known_powers({ k: sub_k, alpha: q_sub_params, Hs: Hs.slice(0, k - 2), field: field });

  const S1 = _poly_add(Hs[k - 1], q_sub, field);
  const S2 = _poly_add_const(Hs[k - 1], alpha[(1 << (k - 1)) - 2], field);

  const a_alpha = alpha.slice(0, (1 << (k - 1)) - 2);
  const beta_block_start = (1 << (k - 1)) + (1 << (k - 2)) - 2;
  const beta_block = alpha.slice(beta_block_start);
  const l = k - 2;
  const need_beta = (1 << l) + 1;
  if (beta_block.length !== need_beta) {
    throw new Error('internal error: beta-block length mismatch');
  }

  const beta = []; // β0..β_{2^l}
  for (let i = 0; i < need_beta; i++) beta.push(field.zero());
  for (let i = 0; i < beta_block.length; i++) beta[(1 << l) - i] = beta_block[i];
  return _poly_paper_A_fill({ l: l, alpha: a_alpha, beta: beta, S1_2l: S1, S2_2l: S2, Hs: Hs.slice(0, l + 1), field: field });
}

// py: tools/poly_schedule.py:3811
// Coefficient-level encoder for the quadratic base polynomial:
//     H2 = (x + alpha1)*x + alpha0 = x^2 + alpha1*x + alpha0.
function _poly_paper_H2({ x, alpha0, alpha1, field }) {
  x = _poly_trim(x, field);
  if (
    _poly_degree(x) !== 1 ||
    !field.eq(_poly_coeff(x, 1, field), field.one()) ||
    !field.eq(_poly_coeff(x, 0, field), field.zero())
  ) {
    throw new Error('_poly_paper_H2 expects x = [0,1]');
  }
  return [field.coerce(alpha0), field.coerce(alpha1), field.one()];
}

// py: tools/poly_schedule.py:3823
// Coefficient-level square-difference gadget: S1^2 - S2^2.
function _poly_square_diff({ S1, S2, field }) {
  return _poly_sub(_poly_square(S1, field), _poly_square(S2, field), field);
}

// py: tools/poly_schedule.py:3829
// Coefficient-level encoder matching `_paper_Q_2lp1k_minus_1_with_powers`.
// Returns:
//   [Q, Hs_out, tilde_out]
function _poly_paper_Q_2lp1k_minus_1_with_powers({ k, l, alpha, Hs, field }) {
  if (k < 0 || l < 1) throw new Error('Q_2lp1k_minus_1 requires k>=0 and l>=1');
  const x = _poly_trim(Hs[0], field);
  if (
    _poly_degree(x) !== 1 ||
    !field.eq(_poly_coeff(x, 1, field), field.one()) ||
    !field.eq(_poly_coeff(x, 0, field), field.zero())
  ) {
    throw new Error('expected Hs[0]=x');
  }

  let deg = (1 << (l + 1)) * k + ((1 << l) - 1);
  if (deg === 0) {
    if (alpha.length !== 1) throw new Error('degree-0 Q requires 1 parameter');
    const z = [field.coerce(alpha[0])];
    return [z, Hs.slice(), z];
  }
  if (alpha.length !== deg) {
    throw new Error(`Q_2lp1k_minus_1(k=${k},l=${l}) needs ${deg} alpha params, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  if (k === 0) {
    const out = _poly_paper_Q_known_powers({ k: l, alpha: alpha, Hs: Hs.slice(0, l), field: field });
    return [out, Hs.slice(), x];
  }

  if (l === 1) {
    // Special case: Q_{4k+1}(x,H2) using a shifted quadratic input and (x+β0) extraction.
    if (Hs.length < 2) throw new Error('Q_2lp1k_minus_1(l=1) requires Hs=[x,H2]');
    deg = 4 * k + 1;
    if (alpha.length !== deg) {
      throw new Error(`Q_2lp1k_minus_1(k=${k},l=1) needs ${deg} alpha params, got ${alpha.length}`);
    }
    const t_params = alpha.slice(0, 4 * k - 2);
    const tilde_shift = alpha[4 * k - 2];
    const hat_shift = alpha[4 * k - 1];
    const beta0 = alpha[4 * k];

    const H2 = _poly_trim(Hs[1], field);
    const H_hat = _poly_add_const(H2, hat_shift, field);
    const tilde_H2 = _poly_add_const(H_hat, tilde_shift, field);

    const [S1, S2, Hs_out, tilde_out] = _poly_paper_T({
      k: 2 * k, l: 1, alpha: t_params, Hs: [x, H_hat], tilde_H_2l: tilde_H2, field: field,
    });
    const out = _poly_add(_poly_mul(_poly_add_const(x, beta0, field), S1, field), S2, field);
    return [_poly_trim(out, field), Hs_out, tilde_out];
  }

  const block = 1 << l;
  const a_alpha = alpha.slice(0, block - 2); // α0..α_{2^l-3}
  const t_start = block - 2;
  const shift_idx = (1 << (l + 1)) * k - 2; // α_{2^{l+1}k-2}
  const t_params = alpha.slice(t_start, shift_idx); // α_{2^l-2}..α_{2^{l+1}k-3}
  const shift = alpha[shift_idx];

  const qhat_start = shift_idx + 1;
  const qhat_len = (1 << (l - 1)) - 1;
  const qhat_params = alpha.slice(qhat_start, qhat_start + qhat_len);

  const beta_start = qhat_start + qhat_len;
  const beta_len = (1 << (l - 1)) + 1;
  const beta_params = alpha.slice(beta_start, beta_start + beta_len);
  if (beta_params.length !== beta_len || beta_start + beta_len !== alpha.length) {
    throw new Error('internal error: beta param count mismatch in Q_2lp1k_minus_1');
  }

  // \hat H_{2^l} = H_{2^l} + Q_{2^{l-1}-1}(...), for l>=2.
  if (Hs.length <= l) {
    throw new Error(`Q_2lp1k_minus_1(l=${l}) requires Hs up to index ${l} (H_{2^${l}})`);
  }
  let H_hat = _poly_trim(Hs[l], field);
  if (l > 1) {
    const qhat = _poly_paper_Q_known_powers({ k: l - 1, alpha: qhat_params, Hs: Hs.slice(0, l - 1), field: field });
    H_hat = _poly_add(H_hat, qhat, field);
  }

  // Run T_{2k,2^l} with H_{2^l} replaced by \hat H_{2^l}.
  const Hs_hat = Hs.slice();
  if (Hs_hat.length <= l) throw new Error('internal error: Hs_hat too short');
  Hs_hat[l] = H_hat;
  const need_t = (2 * k - 1) * block;
  if (t_params.length !== need_t) {
    throw new Error(`internal error: expected ${need_t} T-params, got ${t_params.length}`);
  }
  const [S1, S2, Hs_out, tilde_out] = _poly_paper_T({
    k: 2 * k, l: l, alpha: t_params, Hs: Hs_hat, tilde_H_2l: _poly_add_const(H_hat, shift, field), field: field,
  });

  // Final fill A_{2^{l-1}} on (S1,S2).
  const A_l = l - 1;
  const A_beta = []; // β0..β_{2^{l-1}}
  for (let i = 0; i < (1 << A_l) + 1; i++) A_beta.push(field.zero());
  for (let i = 0; i < beta_params.length; i++) A_beta[(1 << A_l) - i] = beta_params[i];

  const out = _poly_paper_A_fill({ l: A_l, alpha: a_alpha.slice(), beta: A_beta, S1_2l: S1, S2_2l: S2, Hs: Hs.slice(0, A_l + 1), field: field });
  return [_poly_trim(out, field), Hs_out, tilde_out];
}

// py: tools/poly_schedule.py:3933
function _poly_paper_Q_for_odd_degree_with_powers({ deg, alpha, Hs, field }) {
  if (deg < 1 || deg % 2 === 0) throw new Error('Q_for_odd_degree requires odd deg >= 1');
  const l = _v2_positive(deg + 1);
  const odd = (deg + 1) >> l;
  if (odd % 2 === 0) {
    throw new Error('internal error: expected odd factor (deg+1)/2^l to be odd');
  }
  const k = Math.floor((odd - 1) / 2);
  if (PEELED_Q && deg >= 3 && Hs.length >= 32 - Math.clz32(deg) /* deg.bit_length() */) {
    return [_poly_QO({ deg: deg, alpha: alpha, Hs: Hs, field: field }), Hs.slice(), Hs[0]];
  }
  return _poly_paper_Q_2lp1k_minus_1_with_powers({ k: k, l: l, alpha: alpha, Hs: Hs, field: field });
}

// py: tools/poly_schedule.py:3952
// Coefficient-level encoder matching `_paper_P7` for characteristic != 2.
//
//   y = x * (x + α6)
//   z = (α5 + x + y) * (α4 + x)
//   w = (α3 + z) * x
//   v = (α2 + x + z) * (α1 + w)
//   P7 = α0 + y + w + v
function _poly_paper_P7({ alpha, field }) {
  if (alpha.length !== 7) throw new Error(`P7 needs 7 params, got ${alpha.length}`);
  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error('_poly_paper_P7 only implements the char!=2 variant');
  }
  alpha = alpha.map((a) => field.coerce(a));
  const x = [field.zero(), field.one()];

  const y = _poly_mul(x, _poly_add_const(x, alpha[6], field), field);
  const z = _poly_mul(
    _poly_add_const(_poly_add(_poly_add(x, y, field), [alpha[5]], field), field.zero(), field),
    _poly_add_const(x, alpha[4], field),
    field
  );
  const w = _poly_mul(_poly_add_const(z, alpha[3], field), x, field);
  const v = _poly_mul(
    _poly_add_const(_poly_add(x, z, field), alpha[2], field),
    _poly_add_const(w, alpha[1], field),
    field
  );
  const out = _poly_add(_poly_add(_poly_add_const(y, alpha[0], field), w, field), v, field);
  return _poly_trim(out, field);
}

// py: tools/poly_schedule.py:3987
// Coefficient-level encoder matching `_paper_P5`:
//
//   P5[α0..α4](x) = (x + α2) * ( (x^2 + α4) * (x^2 + x + α3) + α1 ) + α0
function _poly_paper_P5({ alpha, field }) {
  if (alpha.length !== 5) throw new Error(`P5 needs 5 params, got ${alpha.length}`);
  alpha = alpha.map((a) => field.coerce(a));
  const x = [field.zero(), field.one()];

  const x2 = _poly_square(x, field);
  const z = _poly_mul(
    _poly_add_const(x2, alpha[4], field),
    _poly_add_const(_poly_add(x2, x, field), alpha[3], field),
    field
  );
  const w = _poly_mul(_poly_add_const(x, alpha[2], field), _poly_add_const(z, alpha[1], field), field);
  const out = _poly_add_const(w, alpha[0], field);
  return _poly_trim(out, field);
}

// py: tools/poly_schedule.py:4006
// Coefficient-level encoder matching `_paper_barQ_15` (special case 31 gadget).
function _poly_paper_barQ_15({ alpha, H2, H4, field }) {
  if (alpha.length !== 15) throw new Error(`barQ_15 needs 15 parameters, got ${alpha.length}`);
  alpha = alpha.map((a) => field.coerce(a));
  const x = [field.zero(), field.one()];

  const a_h8 = alpha[0], b_h8 = alpha[1], c_h8 = alpha[2];
  const d_shift = alpha[3];
  const a_alpha = alpha.slice(4, 10);
  const beta = alpha.slice(10, 15);

  const A = _poly_add_const(x, b_h8, field);
  const B = _poly_add_const(_poly_trim(H2, field), c_h8, field);
  const H8 = _poly_add_const(
    _poly_mul(_poly_add(_poly_trim(H4, field), A, field), _poly_add(_poly_trim(H4, field), B, field), field),
    a_h8,
    field
  );
  const S1 = H8;
  const S2 = _poly_add_const(H8, d_shift, field);
  return _poly_paper_A_fill({ l: 2, alpha: a_alpha.slice(), beta: beta.slice(), S1_2l: S1, S2_2l: S2, Hs: [x, H2, H4], field: field });
}

// py: tools/poly_schedule.py:4033
// Coefficient-level encoder matching `_paper_barQ_8k_plus_7_with_powers`.
// Returns:
//   [barQ, Hs_out]
function _poly_paper_barQ_8k_plus_7_with_powers({ k, alpha, H2, H4, field }) {
  if (k < 2) throw new Error('barQ_{8k+7} requires k>=2');
  const deg = 8 * k + 7;
  if (alpha.length !== deg) {
    throw new Error(`barQ_{8k+7} (k=${k}) needs ${deg} parameters, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  const x = [field.zero(), field.one()];

  const [a_h8, b_h8, c_h8, d_tilde] = alpha.slice(0, 4);
  const t_len = (k - 1) * 8;
  const t_params = alpha.slice(4, 4 + t_len);
  const fill = alpha.slice(4 + t_len);
  const a_alpha = fill.slice(0, 6);
  const beta = fill.slice(6);
  if (a_alpha.length !== 6 || beta.length !== 5) {
    throw new Error('internal error: barQ_{8k+7} fill parameter partition mismatch');
  }

  const H8 = _poly_add_const(
    _poly_mul(
      _poly_add(_poly_trim(H4, field), _poly_add_const(x, b_h8, field), field),
      _poly_add(_poly_trim(H4, field), _poly_add_const(_poly_trim(H2, field), c_h8, field), field),
      field
    ),
    a_h8,
    field
  );
  const tilde_H8 = _poly_add_const(H8, d_tilde, field);

  const [S1, S2, Hs_out, _tilde_out] = _poly_paper_T({
    k: k, l: 3, alpha: t_params, Hs: [x, H2, H4, H8], tilde_H_2l: tilde_H8, field: field,
  });
  const out = _poly_paper_A_fill({ l: 2, alpha: a_alpha.slice(), beta: beta.slice(), S1_2l: S1, S2_2l: S2, Hs: [x, H2, H4], field: field });
  return [_poly_trim(out, field), Hs_out.slice()];
}

// py: tools/poly_schedule.py:4084
// Coefficient-level encoder matching `_paper_barQ_odd_with_H2_H4_with_powers`.
function _poly_paper_barQ_odd_with_H2_H4_with_powers({ deg, alpha, Hs_in, field }) {
  if (deg < 1 || deg % 2 === 0) throw new Error('barQ requires odd deg >= 1');
  if (alpha.length !== deg) {
    throw new Error(`barQ_${deg} needs ${deg} alpha params, got ${alpha.length}`);
  }
  if (Hs_in.length < 2) throw new Error('barQ requires Hs_in=[x,H2,...]');
  alpha = alpha.map((a) => field.coerce(a));

  const l_need = _v2_positive(deg + 1);
  const odd = (deg + 1) >> l_need;
  const kk = Math.floor((odd - 1) / 2);
  const need = kk > 0 ? l_need + 1 : l_need;
  if (Hs_in.length >= need) {
    const [q, Hs_out] = _poly_paper_Q_for_odd_degree_with_powers({ deg: deg, alpha: alpha, Hs: Hs_in, field: field });
    return [_poly_trim(q, field), Hs_out.slice()];
  }

  if (Hs_in.length < 3) throw new Error('barQ fallback requires H4 (Hs_in[2]) to be available');
  const x = _poly_trim(Hs_in[0], field);
  const H2 = _poly_trim(Hs_in[1], field);
  const H4 = _poly_trim(Hs_in[2], field);

  if (deg === 15) {
    return [_poly_paper_barQ_15({ alpha: alpha, H2: H2, H4: H4, field: field }), Hs_in.slice()];
  }

  if (deg % 8 === 7 && deg >= 23) {
    const k = Math.floor((deg - 7) / 8);
    const [out, powers_out] = _poly_paper_barQ_8k_plus_7_with_powers({ k: k, alpha: alpha, H2: H2, H4: H4, field: field });
    const Hs_out = Hs_in.slice();
    if (Hs_out.length < powers_out.length) {
      for (const p of powers_out.slice(Hs_out.length)) Hs_out.push(p);
    }
    return [_poly_trim(out, field), Hs_out];
  }

  throw new Error(
    `internal error: no barQ fallback case matched for deg=${deg} (need=${need}, have=${Hs_in.length})`
  );
}

// py: tools/poly_schedule.py:4133
// Coefficient-level encoder matching `_paper_splittable_pair`.
// Returns:
//   [T1, T2, Hs] where Hs[i] is monic degree 2^i, Hs[0]=x.
function _poly_paper_splittable_pair({ n, alpha, field }) {
  if (n < 1 || n % 2 === 0) throw new Error('splittable_pair requires odd n >= 1');
  if (n === 7) {
    throw new Error('no splittable pair is used for n=7; use the septic base construction instead');
  }
  if (alpha.length !== n) throw new Error(`splittable_pair(${n}) needs ${n} params, got ${alpha.length}`);
  alpha = alpha.map((a) => field.coerce(a));

  const x = [field.zero(), field.one()];

  if (n === 1) {
    return [[field.one()], [alpha[0]], [x]];
  }

  if (n === 3) {
    const H2 = _poly_paper_H2({ x: x, alpha0: alpha[1], alpha1: alpha[2], field: field });
    return [H2, _poly_add_const(H2, alpha[0], field), [x, H2]];
  }

  // Special cases.
  if (n === 15) {
    const H2 = _poly_paper_H2({ x: x, alpha0: alpha[6], alpha1: alpha[7], field: field });
    const x_shift = _poly_add_const(x, alpha[5], field);
    const H4 = _poly_add_const(_poly_square_diff({ S1: H2, S2: x_shift, field: field }), alpha[4], field);

    const S1 = _poly_paper_Q_known_powers({ k: 3, alpha: alpha.slice(8, 15), Hs: [x, H2, H4], field: field });
    const S2 = _poly_add_const(H2, alpha[3], field);
    const T1 = _poly_add_const(_poly_square_diff({ S1: S1, S2: S2, field: field }), alpha[1], field);

    // Easier: T2_low = square_diff(H4, H2+α2) + α0.
    const T2_low = _poly_add_const(
      _poly_square_diff({ S1: H4, S2: _poly_add_const(H2, alpha[2], field), field: field }),
      alpha[0],
      field
    );
    const T2 = _poly_add(T2_low, T1, field);
    const H8 = T2_low;
    return [_poly_trim(T1, field), _poly_trim(T2, field), [x, H2, H4, H8]];
  }

  if (n === 27) {
    const H2 = _poly_paper_H2({ x: x, alpha0: alpha[2], alpha1: alpha[3], field: field });
    const [S1, Hs_out] = _poly_paper_Q_2lp1k_minus_1_with_powers({ k: 3, l: 1, alpha: alpha.slice(14, 27), Hs: [x, H2], field: field });
    if (Hs_out.length <= 2) {
      throw new Error('internal error: expected H4 byproduct in Q_13');
    }
    const H4 = Hs_out[2];
    const Hs = [x, H2].concat(Hs_out.slice(2));

    const S2 = _poly_paper_q3({ alpha0: alpha[4], alpha1: alpha[5], alpha2: alpha[6], H2: H2, field: field });
    const S3 = _poly_paper_Q_known_powers({ k: 3, alpha: alpha.slice(7, 14), Hs: [x, H2, H4], field: field });

    const T1 = _poly_add_const(_poly_square_diff({ S1: S1, S2: S2, field: field }), alpha[1], field);
    const T2_low = _poly_add_const(_poly_square_diff({ S1: S3, S2: H2, field: field }), alpha[0], field);
    const T2 = _poly_add(T2_low, T1, field);
    return [_poly_trim(T1, field), _poly_trim(T2, field), Hs];
  }

  if (n === 31) {
    const H2 = _poly_paper_H2({ x: x, alpha0: alpha[6], alpha1: alpha[7], field: field });
    const x_shift = _poly_add_const(x, alpha[5], field);
    const H4 = _poly_add_const(_poly_square_diff({ S1: H2, S2: x_shift, field: field }), alpha[4], field);

    const [S1] = _poly_paper_barQ_odd_with_H2_H4_with_powers({
      deg: 15, alpha: alpha.slice(16, 31), Hs_in: [x, H2, H4], field: field,
    });
    const S2 = _poly_paper_Q_known_powers({ k: 3, alpha: alpha.slice(8, 15), Hs: [x, H2, H4], field: field });
    const S3 = _poly_paper_q3({ alpha0: alpha[1], alpha1: alpha[2], alpha2: alpha[3], H2: H2, field: field });
    const T1 = _poly_add(_poly_square_diff({ S1: S1, S2: S2, field: field }), S3, field);

    const T2 = _poly_add_const(
      _poly_square_diff({ S1: _poly_add_const(S1, alpha[15], field), S2: H4, field: field }),
      alpha[0],
      field
    );
    return [_poly_trim(T1, field), _poly_trim(T2, field), [x, H2, H4]];
  }

  // Main families.
  if (n % 4 === 1) {
    const k = Math.floor((n - 1) / 4);
    const t_params = alpha.slice(0, n - 3);
    const tilde_shift = alpha[n - 3];
    const h2_const = alpha[n - 2];
    const h2_lin = alpha[n - 1];

    const H2 = _poly_paper_H2({ x: x, alpha0: h2_const, alpha1: h2_lin, field: field });
    const tilde_H2 = _poly_add_const(H2, tilde_shift, field);
    const [T1, T2, Hs_out] = _poly_paper_T({ k: 2 * k, l: 1, alpha: t_params, Hs: [x, H2], tilde_H_2l: tilde_H2, field: field });
    return [_poly_trim(T1, field), _poly_trim(T2, field), Hs_out];
  }

  if (n % 8 === 3) {
    const k = Math.floor((n - 3) / 8);
    const sub_n = 2 * k + 1;
    const [S1_1, S1_2, Hs] = _poly_paper_splittable_pair({ n: sub_n, alpha: alpha.slice(2 * k, 4 * k + 1), field: field });
    if (Hs.length < 2) {
      throw new Error('internal error: expected H2 in splittable_pair output');
    }
    const H2 = Hs[1];

    const [S2, Hs2_raw] = _poly_paper_Q_2lp1k_minus_1_with_powers({ k: k, l: 1, alpha: alpha.slice(4 * k + 2, 8 * k + 3), Hs: [x, H2], field: field });
    if (Hs2_raw.length <= 2) {
      throw new Error('internal error: expected an H4 byproduct in Q_{4k+1}');
    }
    let Hs2 = [x, H2].concat(Hs2_raw.slice(2));

    let S3, Hs3;
    if (k === 1) {
      S3 = [alpha[1]];
      Hs3 = Hs2.slice();
    } else {
      const deg3 = 2 * k - 1;
      const res3 = _poly_paper_Q_for_odd_degree_with_powers({ deg: deg3, alpha: alpha.slice(1, 2 * k), Hs: Hs2, field: field });
      S3 = res3[0];
      Hs3 = res3[1];
    }

    if (Hs.length > Hs2.length) {
      Hs2 = Hs2.slice().concat(Hs.slice(Hs2.length));
    }
    if (Hs3.length > Hs2.length) {
      Hs2 = Hs2.slice().concat(Hs3.slice(Hs2.length));
    }

    const T1 = _poly_add(_poly_square_diff({ S1: S2, S2: S1_1, field: field }), S3, field);
    const T2 = _poly_add_const(
      _poly_square_diff({ S1: _poly_add_const(S2, alpha[4 * k + 1], field), S2: S1_2, field: field }),
      alpha[0],
      field
    );
    return [_poly_trim(T1, field), _poly_trim(T2, field), Hs2];
  }

  if (n % 8 === 7) {
    const k = Math.floor((n - 7) / 8);
    const sub_n = 2 * k + 1;
    let [S1_1, S1_2, Hs] = _poly_paper_splittable_pair({ n: sub_n, alpha: alpha.slice(0, 2 * k + 1), field: field });
    if (Hs.length < 2) {
      throw new Error('internal error: expected H2 in splittable_pair output for 8k+7 case');
    }
    const H2 = Hs[1];

    function build_Q({ deg, params, Hs_in }) {
      const l = _v2_positive(deg + 1);
      const odd = (deg + 1) >> l;
      const kk = Math.floor((odd - 1) / 2);
      const need = kk > 0 ? l + 1 : l;
      if (Hs_in.length >= need) {
        const [q, Hs_out] = _poly_paper_Q_for_odd_degree_with_powers({ deg: deg, alpha: params, Hs: Hs_in, field: field });
        return [_poly_trim(q, field), Hs_out.slice()];
      }
      const [q, Hs_out] = _poly_paper_barQ_odd_with_H2_H4_with_powers({ deg: deg, alpha: params, Hs_in: Hs_in, field: field });
      return [_poly_trim(q, field), Hs_out.slice()];
    }

    // S2 = Q_{2k+1}[...].
    let res = build_Q({ deg: sub_n, params: alpha.slice(2 * k + 2, 4 * k + 3), Hs_in: Hs });
    const S2 = res[0];
    Hs = res[1];
    if (Hs.length < 3) {
      throw new Error('internal error: expected H4 to remain available after Q_{2k+1}');
    }

    // S3 = Q_{4k+3}[...].
    res = build_Q({ deg: 4 * k + 3, params: alpha.slice(4 * k + 4, 8 * k + 7), Hs_in: Hs });
    const S3 = res[0];
    Hs = res[1];

    const T1 = _poly_add(_poly_square_diff({ S1: S3, S2: S2, field: field }), S1_1, field);
    const S2_shift = _poly_add_const(S2, alpha[2 * k + 1], field);
    const S3_shift = _poly_add_const(S3, alpha[4 * k + 3], field);
    const T2 = _poly_add(_poly_square_diff({ S1: S3_shift, S2: S2_shift, field: field }), S1_2, field);
    return [_poly_trim(T1, field), _poly_trim(T2, field), Hs];
  }

  throw new Error(`internal error: no splittable case matched for odd n=${n}`);
}

// py: tools/poly_schedule.py:4296
// Coefficient-level encoder for the full paper family P_n[α].
// Returns coefficient list [a0..a_{n-1}, 1] for the monic polynomial of degree n.
function _poly_paper_P_from_params({ params, field }) {
  if (params.length === 0) throw new Error('params must be non-empty');
  params = params.map((a) => field.coerce(a));
  const n = params.length;

  const x = [field.zero(), field.one()];
  if (n === 1) {
    return _poly_add_const(x, params[0], field);
  }
  if (n === 5) {
    return _poly_paper_P5({ alpha: params, field: field });
  }
  if (n === 7) {
    return _poly_paper_P7({ alpha: params, field: field });
  }
  if (n % 2 === 0) {
    // P_n = α0 + x*P_{n-1}(α1..)
    const q = _poly_paper_P_from_params({ params: params.slice(1), field: field });
    return _poly_add_const(_poly_mul(q, x, field), params[0], field);
  }

  const [T1, T2] = _poly_paper_splittable_pair({ n: n, alpha: params, field: field });
  return _poly_add(_poly_mul(T1, x, field), T2, field);
}

// py: tools/poly_schedule.py:4324
// Coefficient-level encoder matching `_paper_T` (splittable-pair recursion).
//
// This is intended for coefficient-level decoding routines that need to
// re-materialize tail-only / zero-parameter instances (paper "derivable"
// polynomials) without using probing.
//
// Currently only supports char(F) != 2.
// Returns:
//   [T1, T2, Hs_out, tilde_out]
function _poly_paper_T({ k, l, alpha, Hs, tilde_H_2l, field }) {
  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error('_poly_paper_T is not implemented for char(F)=2');
  }

  if (k < 1) throw new Error('T requires k >= 1');
  if (l < 1) throw new Error('T requires l >= 1');
  if (Hs.length <= l) {
    throw new Error(`T(k=${k},l=${l}) requires Hs up to index ${l} (H_{2^${l}})`);
  }

  const block = 1 << l;
  const need = (k - 1) * block;
  if (alpha.length !== need) {
    throw new Error(`T(k=${k},l=${l}) needs ${k - 1}*2^${l}=${need} alpha params, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  const x = _poly_trim(Hs[0], field);
  tilde_H_2l = _poly_trim(tilde_H_2l, field);

  if (k === 1) {
    return [_poly_trim(Hs[l], field), tilde_H_2l, Hs.slice(), tilde_H_2l];
  }

  // Even k
  if (k % 2 === 0) {
    const rec_len = (Math.floor(k / 2) - 1) * (2 * block);
    const tail = alpha.slice(rec_len);
    const rec_params = alpha.slice(0, rec_len);
    if (tail.length !== block) {
      throw new Error('internal error: T even tail length mismatch');
    }

    if (l === 1) {
      const a0 = tail[0], a1 = tail[1];
      const H2 = _poly_trim(Hs[1], field);
      const x_plus = _poly_add_const(x, a1, field);
      const H4 = _poly_add(_poly_sub(_poly_square(H2, field), _poly_square(x_plus, field), field), [a0], field);
      const Ht2 = _poly_trim(tilde_H_2l, field);
      const delta = _poly_sub(Ht2, H2, field);
      if (_poly_trim(delta, field).length > 1) {
        throw new Error('The shared l=1 base requires tilde_H2-H2 to be scalar');
      }
      const tilde_H4 = _poly_add(H4, delta, field);

      const Hs_next = Hs.slice();
      while (Hs_next.length < 3) Hs_next.push([field.zero()]);
      Hs_next[2] = _poly_trim(H4, field);
      return _poly_paper_T({
        k: Math.floor(k / 2), l: l + 1, alpha: rec_params, Hs: Hs_next, tilde_H_2l: tilde_H4, field: field,
      });
    }

    // l >= 2
    const half = 1 << (l - 1);
    const q_hi = _poly_paper_Q_known_powers({ k: l - 1, alpha: tail.slice(half + 1), Hs: Hs.slice(0, l - 1), field: field });
    const q_lo = _poly_paper_Q_known_powers({ k: l - 1, alpha: tail.slice(1, half), Hs: Hs.slice(0, l - 1), field: field });

    const S1_1 = _poly_add(Hs[l - 1], q_hi, field);
    const S1_2 = _poly_trim(q_lo, field);
    const H_next = _poly_add(_poly_mul(_poly_add(Hs[l], S1_1, field), _poly_sub(Hs[l], S1_1, field), field), S1_2, field);

    const S2_1 = _poly_add_const(Hs[l - 1], tail[half], field);
    const S2_2 = [tail[0]];
    const tilde_next = _poly_add(
      _poly_mul(_poly_add(tilde_H_2l, S2_1, field), _poly_sub(tilde_H_2l, S2_1, field), field),
      S2_2,
      field
    );

    const Hs_next = Hs.slice();
    while (Hs_next.length < l + 2) Hs_next.push([field.zero()]);
    Hs_next[l + 1] = _poly_trim(H_next, field);
    return _poly_paper_T({
      k: Math.floor(k / 2), l: l + 1, alpha: rec_params, Hs: Hs_next, tilde_H_2l: tilde_next, field: field,
    });
  }

  // Odd k
  const m = Math.floor((k - 1) / 2);
  if (l === 2) {
    if (block !== 4) throw new Error('internal error: expected block=4 for l=2');
    const head = alpha.slice(0, 4);
    const tail = alpha.slice(alpha.length - 4);
    const mid = alpha.slice(4, alpha.length - 4);

    const H2 = _poly_trim(Hs[1], field);
    const H4 = _poly_trim(Hs[2], field);

    // Tail parameters follow the shared-product odd base:
    //   tail[0]=α_{4k-8} : shift from H8 to tilde_H8
    //   tail[1]=α_{4k-7} : S1_3
    //   tail[2]=α_{4k-6} : S1_2 shift in (x+α)
    //   tail[3]=α_{4k-5} : shift in S1_1 = H2 + (x+α)
    const next_shift = tail[0], s1_3 = tail[1], s1_2_shift = tail[2], s1_1_shift = tail[3];

    // First branch:
    //   S1_1 = H2 + (x + s1_1_shift)
    //   S1_2 = x + s1_2_shift
    //   S1_3 = s1_3
    const S1_1 = _poly_add(H2, _poly_add_const(x, s1_1_shift, field), field);
    const core = _poly_add(H4, S1_1, field);
    const S1_2 = _poly_add_const(x, s1_2_shift, field);
    const H8 = _poly_add(
      _poly_mul(_poly_add(core, S1_2, field), _poly_sub(core, S1_2, field), field),
      [s1_3],
      field
    );

    const Hs_next = Hs.slice();
    while (Hs_next.length < 4) Hs_next.push([field.zero()]);
    Hs_next[3] = _poly_trim(H8, field);

    const rho = _poly_sub(_poly_trim(tilde_H_2l, field), H4, field);
    if (_poly_trim(rho, field).length > 1) {
      throw new Error('The shared odd l=2 base requires tilde_H4-H4 to be scalar');
    }
    const S2_1 = _poly_sub(S1_1, rho, field);
    const tilde_H8 = _poly_add(H8, [next_shift], field);

    const [T1_rec, T2_rec, Hs_out, tilde_out] = _poly_paper_T({
      k: m, l: l + 1, alpha: mid, Hs: Hs_next, tilde_H_2l: tilde_H8, field: field,
    });

    const q3 = _poly_paper_Q_known_powers({ k: 2, alpha: head.slice(1), Hs: Hs.slice(0, 2), field: field });
    const factor1 = _poly_sub(H4, _poly_scale_int(S1_1, k - 1, field), field);
    const T1 = _poly_add(_poly_mul(factor1, T1_rec, field), q3, field);

    const factor2 = _poly_sub(_poly_trim(tilde_H_2l, field), _poly_scale_int(S2_1, k - 1, field), field);
    const T2 = _poly_add_const(_poly_mul(factor2, T2_rec, field), head[0], field);
    return [_poly_trim(T1, field), _poly_trim(T2, field), Hs_out, tilde_out];
  }

  if (l < 3) throw new Error('T odd case requires l >= 3 (or special l=2)');

  const head = alpha.slice(0, block);
  const tail = alpha.slice(alpha.length - block);
  const mid = alpha.slice(block, alpha.length - block);
  const half = 1 << (l - 1);
  const quarter = 1 << (l - 2);

  const q_hi = _poly_paper_Q_known_powers({ k: l - 1, alpha: tail.slice(half + 1), Hs: Hs.slice(0, l - 1), field: field });
  const S1_1 = _poly_add(Hs[l - 1], q_hi, field);

  const q_mid = _poly_paper_Q_known_powers({ k: l - 2, alpha: tail.slice(quarter + 1, half), Hs: Hs.slice(0, l - 2), field: field });
  const S1_2 = _poly_add(Hs[l - 2], q_mid, field);

  const S1_3 = _poly_paper_Q_known_powers({ k: l - 2, alpha: tail.slice(1, quarter), Hs: Hs.slice(0, l - 2), field: field });

  const base = _poly_add(Hs[l], S1_1, field);
  const H_next = _poly_add(_poly_mul(_poly_add(base, S1_2, field), _poly_sub(base, S1_2, field), field), S1_3, field);

  const S2_1 = _poly_add_const(Hs[l - 1], tail[half], field);
  const S2_2 = _poly_add_const(Hs[l - 2], tail[quarter], field);
  const S2_3 = [tail[0]];
  const base2 = _poly_add(tilde_H_2l, S2_1, field);
  const tilde_next = _poly_add(_poly_mul(_poly_add(base2, S2_2, field), _poly_sub(base2, S2_2, field), field), S2_3, field);

  const Hs_next = Hs.slice();
  while (Hs_next.length < l + 2) Hs_next.push([field.zero()]);
  Hs_next[l + 1] = _poly_trim(H_next, field);

  const [T1_rec, T2_rec, Hs_out, tilde_out] = _poly_paper_T({
    k: m, l: l + 1, alpha: mid, Hs: Hs_next, tilde_H_2l: tilde_next, field: field,
  });

  const q_low = _poly_paper_Q_known_powers({ k: l, alpha: head.slice(1), Hs: Hs.slice(0, l), field: field });
  const factor1 = _poly_sub(Hs[l], _poly_scale_int(S1_1, k - 1, field), field);
  const T1 = _poly_add(_poly_mul(factor1, T1_rec, field), q_low, field);

  const factor2 = _poly_sub(tilde_H_2l, _poly_scale_int(S2_1, k - 1, field), field);
  const T2 = _poly_add_const(_poly_mul(factor2, T2_rec, field), head[0], field);
  return [_poly_trim(T1, field), _poly_trim(T2, field), Hs_out, tilde_out];
}

// py: tools/poly_schedule.py:4515
// Compute the proof-remainder polynomial:
//     P_R := x (T^{(1)}_{k,2^l} - H_{2^l}^k) + (T^{(2)}_{k,2^l} - \tilde H_{2^l}^k)
// for the coefficient-level `_poly_paper_T` encoder.
function _poly_remainder_poly_from_T({ k, l, alpha, Hs, tilde_H_2l, field }) {
  const x = _poly_trim(Hs[0], field);
  const H_base = _poly_trim(Hs[l], field);
  const [T1, T2] = _poly_paper_T({ k: k, l: l, alpha: alpha, Hs: Hs, tilde_H_2l: tilde_H_2l, field: field });

  const H_pow = _poly_pow(H_base, k, field);
  const Ht_pow = _poly_pow(_poly_trim(tilde_H_2l, field), k, field);
  const left = _poly_shift_xk(_poly_sub(T1, H_pow, field), 1, field);
  const right = _poly_sub(T2, Ht_pow, field);
  return _poly_add(left, right, field);
}

// ====================================================================
// BEGIN g4_decode_prims.frag.js
// ====================================================================
// g4_decode_prims.frag.js — decoder primitives from tools/poly_schedule.py.
// Fragment: function declarations only. Assembled into core.js after
// runtime.frag.js (Field, poly helpers, makeRng, PEELED_Q are in scope).
// Cross-group calls: _poly_paper_Q_2lp1k_minus_1_with_powers,
// _poly_paper_Q_known_powers (both g3, kwarg-only -> options object).

// g4 private helper: Python dict.get(key, default) over a Map.
function _g4_get(m, k, dflt) {
  return m.has(k) ? m.get(k) : dflt;
}

// py: tools/poly_schedule.py:2544
// Decode the "square gadget" from `sections/constructions.tex`, Lemma
// `lem:square-gadget`.
//
// Given a polynomial of the form
//     G = x*S^2 + (S + δ)^2 + E
// where S is monic of degree d and deg(E) <= d,
// recover (S, δ) assuming:
//   - char(F) != 2,
//   - and `boundary_error_coeff_deg_d` equals coeff(E, d) (defaults to 0).
//
// This matches how the lemma is used in the induction-step decoders, where
// the additive error term may have degree exactly d but its degree-d
// coefficient is known/derivable from surrounding structure.
// Returns [S, delta].
function _decode_square_gadget({ G, field, boundary_error_coeff_deg_d = null }) {
  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error('square gadget decoding requires char(F) != 2');
  }
  const inv2 = field.inv(two);

  G = _poly_trim(G, field);
  const degG = _poly_degree(G);
  if (degG < 3 || degG % 2 === 0) {
    throw new Error('square gadget expects odd degree >= 3');
  }
  if (!field.eq(_poly_coeff(G, degG, field), field.one())) {
    throw new Error('square gadget polynomial must be monic');
  }

  const d = Math.floor((degG - 1) / 2);
  if (boundary_error_coeff_deg_d === null) {
    boundary_error_coeff_deg_d = field.zero();
  }

  // Recover the coefficients of A = S^2 in degrees [d..2d] from the identities
  //   [x^i]G = A_{i-1} + A_i  for i=d+1..2d+1,
  // which are unaffected by the low-degree error term E.
  const A_high = new Map([[2 * d, field.one()]]); // Map<degree, field element>
  for (let i = 2 * d + 1; i > d; i--) { // i=2d+1 .. d+1
    const A_i = _g4_get(A_high, i, field.zero());
    const A_im1 = field.sub(_poly_coeff(G, i, field), A_i);
    A_high.set(i - 1, A_im1);
  }

  const A_partial = [];
  for (let j = 0; j < 2 * d + 1; j++) A_partial.push(field.zero());
  for (let j = d; j <= 2 * d; j++) {
    A_partial[j] = _g4_get(A_high, j, field.zero());
  }
  // Ensure monic at top.
  A_partial[2 * d] = field.one();

  const S = _monic_sqrt_from_high_square_coeffs(A_partial, d, field);
  const S_sq = _poly_square(S, field);

  // δ from the boundary coefficient at degree d:
  //   (G - x*S^2 - S^2)[d] = 2δ + E[d].
  const xS_sq = _poly_shift_xk(S_sq, 1, field);
  const D = _poly_sub(_poly_sub(G, xS_sq, field), S_sq, field);
  const coeff_D_d = _poly_coeff(D, d, field);
  const delta = field.mul(
    field.sub(coeff_D_d, field.coerce(boundary_error_coeff_deg_d)),
    inv2
  );

  return [S, delta];
}

// py: tools/poly_schedule.py:2889
// Coefficient-level version of `sections/constructions.tex`, Lemma
// `lem:peel-monic-factor`.
//
// Recover coefficients of a monic polynomial U of degree `factor_deg` from the
// *high* coefficients of the product P = U * known_factor, where
// `known_factor` is monic.
//
// Returns:
//     Map<degree, field element> mapping degrees -> coeff(U, degree) for
//     degrees in [min_deg..factor_deg] (inclusive), always including degree
//     `factor_deg` with coefficient 1.  (Python returns Dict[int, Number];
//     consumers use .items() / .get(deg, default) — iterate the Map with
//     for..of and read with _g4_get.)
function _recover_monic_factor_high_coeffs_from_product({
  product,
  known_factor,
  factor_deg,
  min_deg,
  field,
}) {
  if (min_deg > factor_deg) {
    throw new Error('min_deg must be <= factor_deg');
  }
  known_factor = _poly_trim(known_factor, field);
  product = _poly_trim(product, field);

  const degH = _poly_degree(known_factor);
  if (!field.eq(_poly_coeff(known_factor, degH, field), field.one())) {
    throw new Error('known_factor must be monic');
  }

  const U = new Map([[factor_deg, field.one()]]);
  for (let u_deg = factor_deg - 1; u_deg >= min_deg; u_deg--) {
    const p_deg = degH + u_deg;
    const target = _poly_coeff(product, p_deg, field);
    let known_sum = field.zero();

    // P_{degH+u_deg} = U_{u_deg} + sum_{j=1..t} U_{u_deg+j} * H_{degH-j}
    for (let j = 1; j <= factor_deg - u_deg; j++) {
      known_sum = field.add(
        known_sum,
        field.mul(U.get(u_deg + j), _poly_coeff(known_factor, degH - j, field))
      );
    }

    U.set(u_deg, field.sub(target, known_sum));
  }

  return U;
}

// py: tools/poly_schedule.py:2935
// Extract the scalar shift δ from Lemma `lem:scalar-shift-square`.
//
// Given:
//   - H monic degree d
//   - M monic degree e
//   - λ != 0
//   - coeff(P, d+e) where P = λ (H+δ)^2 M + E and deg(E) <= d+e-1
//
// Return:
//   δ
function _scalar_shift_from_square_boundary({ coeff_P_at_boundary, H, M, lam, field }) {
  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error('scalar-shift-square requires char(F) != 2');
  }
  if (field.is_zero(lam)) {
    throw new Error('lam must be nonzero');
  }

  H = _poly_trim(H, field);
  M = _poly_trim(M, field);
  const d = _poly_degree(H);
  const e = _poly_degree(M);
  if (!field.eq(_poly_coeff(H, d, field), field.one())) {
    throw new Error('H must be monic');
  }
  if (!field.eq(_poly_coeff(M, e, field), field.one())) {
    throw new Error('M must be monic');
  }

  // Compute coeff(H^2 * M, d+e).
  const H_sq = _poly_square(H, field);
  const boundary_deg = d + e;
  let coeff_H2M = field.zero();
  // coeff(H^2 M, boundary) = sum_i H_sq[i] * M[boundary-i]
  for (
    let i = Math.max(0, boundary_deg - e);
    i <= Math.min(boundary_deg, _poly_degree(H_sq));
    i++
  ) {
    coeff_H2M = field.add(
      coeff_H2M,
      field.mul(_poly_coeff(H_sq, i, field), _poly_coeff(M, boundary_deg - i, field))
    );
  }

  const num = field.sub(coeff_P_at_boundary, field.mul(lam, coeff_H2M));
  const den = field.mul(two, lam);
  return field.div(num, den);
}

// py: tools/poly_schedule.py:2987
// Random field element for probing (small integers in the rational case).
function _field_rand(field, rng) {
  if (field.modulus !== null) {
    // Python draws rng.randrange(p) directly; p exceeds Number range here, so
    // compose two 30-bit draws and reduce mod p via coerce.  Exact values need
    // not match Python (the callers self-verify; see makeRng note).
    const hi = rng.randrange(0, 1073741824); // 2^30
    const lo = rng.randrange(0, 1073741824); // 2^30
    return field.coerce((BigInt(hi) << 30n) | BigInt(lo));
  }
  return field.coerce(rng.randrange(-9, 10));
}

// py: tools/poly_schedule.py:2995
// Solve M x = rhs over `field` (M is r x c with r >= c).  Returns x, or null
// if M does not have full column rank.  Small dense elimination; the systems
// here have at most a handful of unknowns (the paper's 2x2 / 3x3 blocks).
function _field_gauss_solve(M, rhs, field) {
  const rows = M.map((row, idx) => row.concat([rhs[idx]]));
  const ncols = M.length ? M[0].length : 0;
  const piv_rows = [];
  for (let col = 0; col < ncols; col++) {
    let piv = null;
    for (const r of rows) {
      if (!field.is_zero(r[col])) {
        piv = r;
        break;
      }
    }
    if (piv === null) return null;
    rows.splice(rows.indexOf(piv), 1);
    const inv = field.inv(piv[col]);
    piv = piv.map((v) => field.mul(v, inv));
    for (const r of rows) {
      const f = r[col];
      if (!field.is_zero(f)) {
        for (let j = col; j <= ncols; j++) {
          r[j] = field.sub(r[j], field.mul(f, piv[j]));
        }
      }
    }
    piv_rows.push(piv);
  }
  // Back-substitute.
  const x = [];
  for (let i = 0; i < ncols; i++) x.push(field.zero());
  for (let col = ncols - 1; col >= 0; col--) {
    const r = piv_rows[col];
    let acc = r[ncols];
    for (let j = col + 1; j < ncols; j++) {
      acc = field.sub(acc, field.mul(r[j], x[j]));
    }
    x[col] = acc;
  }
  return x;
}

// py: tools/poly_schedule.py:3033
// Generic structural decoder for the paper's "descending affine pivot" maps.
//
// The paper's decoding lemmas (e.g. `lem:Q-unitriangular`, the pivot tables in
// `lem:4k+1-splittable` / `lem:Rk2l`, and the small linear blocks in
// `lem:barQ15` / `lem:septic-base`) all have the same shape: processing the
// coefficients of the output polynomial from high to low degree, each new
// coefficient exposes one fresh parameter affinely with a constant slope --
// or, occasionally, a small group of parameters that a constant affine system
// over a few otherwise-unused coefficient rows determines (the 2x2/3x3
// blocks).  This routine realizes that procedure numerically for an arbitrary
// encoder `encode_fn: params -> Poly`:
//
//   1. probe the encoder at two random points to find, for every parameter,
//      the set of coefficient rows it touches and its (constant) slopes;
//   2. eliminate parameters from the highest pivot row downwards, solving
//      collided pivot rows as small affine blocks over rows not touched by
//      any other unresolved parameter;
//   3. verify the result by re-encoding (raise `ValueError` on failure).
//
// `rows`, if given, restricts the usable coefficient window (used when only a
// window of the target polynomial is known, cf. the square-gadget steps).
function _decode_by_descending_pivots({
  target,
  encode_fn,
  nparams,
  field,
  rows = null,
  seed = 0,
  what = 'map',
}) {
  const rng = makeRng(0xc0ffee ^ seed ^ (nparams << 8));
  const allowed = rows === null ? null : new Set(rows);

  const bases = [];
  for (let t = 0; t < 2; t++) {
    const b = [];
    for (let i = 0; i < nparams; i++) b.push(_field_rand(field, rng));
    bases.push(b);
  }
  const enc_bases = bases.map((b) => encode_fn(b));

  // diffs[i][t]: row -> slope of parameter i probed at base t.
  const diffs = []; // Array<[Map<row, slope>, Map<row, slope>]>
  const support = []; // Array<Set<row>>
  for (let i = 0; i < nparams; i++) {
    const per_base = [];
    const sup = new Set();
    for (let t = 0; t < 2; t++) {
      const b2 = bases[t].slice();
      b2[i] = field.add(b2[i], field.one());
      const d = _poly_sub(encode_fn(b2), enc_bases[t], field);
      const entries = new Map();
      for (let deg = 0; deg < d.length; deg++) {
        if (!field.is_zero(d[deg])) {
          entries.set(deg, d[deg]);
          sup.add(deg);
        }
      }
      per_base.push(entries);
    }
    diffs.push(per_base);
    support.push(sup);
  }

  const piv_row = [];
  for (let i = 0; i < nparams; i++) {
    let cand;
    if (allowed === null) {
      cand = support[i];
    } else {
      cand = new Set();
      for (const w of support[i]) if (allowed.has(w)) cand.add(w);
    }
    if (cand.size === 0) {
      throw new Error(
        `${what}: parameter ${i} has no effect on the available coefficient window`
      );
    }
    let mx = null;
    for (const w of cand) if (mx === null || w > mx) mx = w;
    piv_row.push(mx);
  }

  // (The Python source defines _diff_vec twice, identically; one suffices.)
  function _diff_vec(a, b) {
    const d = _poly_sub(a, b, field);
    const out = new Map();
    for (let i = 0; i < d.length; i++) {
      if (!field.is_zero(d[i])) out.set(i, d[i]);
    }
    return out;
  }

  const recovered = [];
  for (let i = 0; i < nparams; i++) recovered.push(field.zero());
  const unresolved = new Set();
  for (let i = 0; i < nparams; i++) unresolved.add(i);

  while (unresolved.size > 0) {
    let r = null;
    for (const i of unresolved) if (r === null || piv_row[i] > r) r = piv_row[i];
    let group = [];
    for (const i of unresolved) if (piv_row[i] === r) group.push(i);
    group.sort((a, b) => a - b);

    // Slopes are evaluated lazily at the *current* partial point: by the
    // time a pivot block is reached, all higher-pivot parameters are known,
    // so the block acts affinely there with the constant slopes the paper's
    // pivot lemmas provide.
    const base_now = encode_fn(recovered);
    const cols = new Map(); // param index -> Map<row, slope>

    const _col = (i) => {
      if (!cols.has(i)) {
        const probe = recovered.slice();
        probe[i] = field.add(probe[i], field.one());
        cols.set(i, _diff_vec(encode_fn(probe), base_now));
      }
      return cols.get(i);
    };

    // Grow the block downwards (merging lower pivot groups) until enough
    // clean affine equation rows exist -- the numerical analogue of the
    // paper's small linear blocks (e.g. the 2x2 solve in `lem:barQ15`).
    while (true) {
      const others = [];
      for (const i of unresolved) if (!group.includes(i)) others.push(i);
      let candidates = [];
      for (let w = r; w >= 0; w--) {
        if (allowed !== null && !allowed.has(w)) continue;
        if (others.some((j) => support[j].has(w))) continue;
        if (group.every((i) => field.is_zero(_g4_get(_col(i), w, field.zero())))) continue;
        candidates.push(w);
        if (candidates.length >= group.length + 6) break;
      }

      // Affineness checks on the candidate rows (cheap when the initial
      // two-point probe already agreed there).
      const bad_rows = new Set();
      for (const i of group) {
        const needs_check = candidates.some(
          (w) =>
            !field.eq(_g4_get(diffs[i][0], w, field.zero()), _g4_get(_col(i), w, field.zero())) ||
            !field.eq(_g4_get(diffs[i][1], w, field.zero()), _g4_get(_col(i), w, field.zero()))
        );
        if (!needs_check) continue;
        const probe = recovered.slice();
        probe[i] = field.add(probe[i], field.add(field.one(), field.one()));
        const d2 = _diff_vec(encode_fn(probe), base_now);
        for (const w of candidates) {
          const s = _g4_get(_col(i), w, field.zero());
          if (!field.eq(_g4_get(d2, w, field.zero()), field.add(s, s))) {
            bad_rows.add(w);
          }
        }
      }
      if (group.length <= 8) {
        for (let ai = 0; ai < group.length; ai++) {
          for (let bi = ai + 1; bi < group.length; bi++) {
            const i = group[ai];
            const j = group[bi];
            const probe = recovered.slice();
            probe[i] = field.add(probe[i], field.one());
            probe[j] = field.add(probe[j], field.one());
            const dij = _diff_vec(encode_fn(probe), base_now);
            for (const w of candidates) {
              const want = field.add(
                _g4_get(_col(i), w, field.zero()),
                _g4_get(_col(j), w, field.zero())
              );
              if (!field.eq(_g4_get(dij, w, field.zero()), want)) {
                bad_rows.add(w);
              }
            }
          }
        }
      }
      candidates = candidates.filter((w) => !bad_rows.has(w));

      let solved = false;
      if (candidates.length >= group.length) {
        const M = candidates.map((w) => group.map((i) => _g4_get(_col(i), w, field.zero())));
        const rhs = candidates.map((w) =>
          field.sub(_poly_coeff(target, w, field), _poly_coeff(base_now, w, field))
        );
        const sol = _field_gauss_solve(M, rhs, field);
        if (sol !== null) {
          for (let t = 0; t < group.length; t++) {
            recovered[group[t]] = sol[t];
            unresolved.delete(group[t]);
          }
          solved = true;
        }
      }
      if (solved) break;
      if (others.length === 0) {
        throw new Error(`${what}: not enough clean rows to solve pivot group at degree ${r}`);
      }
      let r_next = null;
      for (const i of others) if (r_next === null || piv_row[i] > r_next) r_next = piv_row[i];
      group = group.concat(others.filter((i) => piv_row[i] === r_next));
      group.sort((a, b) => a - b);
    }
  }

  const chk = encode_fn(recovered);
  if (allowed === null) {
    if (!_poly_eq(chk, target, field)) {
      throw new Error(`${what}: descending-pivot decode failed verification`);
    }
  } else {
    for (const w of allowed) {
      if (!field.eq(_poly_coeff(chk, w, field), _poly_coeff(target, w, field))) {
        throw new Error(`${what}: descending-pivot decode failed verification (row ${w})`);
      }
    }
  }
  return recovered;
}

// py: tools/poly_schedule.py:3503
// Decode the `Q_5[α0..α4](x,H2)` instance that arises as the k=1, l=1 case of
// `_paper_Q_2lp1k_minus_1_with_powers` (Lemma `lem:Q4k+1-from-H2` with k=1),
// by the lemma's descending affine pivots (via `_decode_by_descending_pivots`).
function _decode_Q5_coeffs_to_alpha_given_H2(Q5, H2, field) {
  Q5 = _poly_trim(Q5, field);
  H2 = _poly_trim(H2, field);
  if (_poly_degree(Q5) !== 5 || !field.eq(_poly_coeff(Q5, 5, field), field.one())) {
    throw new Error('Q5 decoder expects a monic degree-5 polynomial');
  }
  if (_poly_degree(H2) !== 2 || !field.eq(_poly_coeff(H2, 2, field), field.one())) {
    throw new Error('Q5 decoder expects monic degree-2 H2');
  }

  const x = [field.zero(), field.one()];

  const _enc = (a) => {
    const [out, _hs, _tilde] = _poly_paper_Q_2lp1k_minus_1_with_powers({
      k: 1,
      l: 1,
      alpha: a.slice(),
      Hs: [x, H2],
      field,
    });
    return out;
  };

  return _decode_by_descending_pivots({
    target: Q5,
    encode_fn: _enc,
    nparams: 5,
    field,
    what: 'Q5-given-H2',
  });
}

// py: tools/poly_schedule.py:3526
// Decode `Q_3[α0,α1,α2](x,H2) = (x+α2)(H2+α1) + α0` given monic quadratic H2.
//
// This matches the direct algebra in sections/constructions.tex.
function _decode_Q3_coeffs_to_alpha_given_H2(Q3, H2, field) {
  Q3 = _poly_trim(Q3, field);
  H2 = _poly_trim(H2, field);
  if (_poly_degree(Q3) !== 3 || !field.eq(_poly_coeff(Q3, 3, field), field.one())) {
    throw new Error('Q3 decoder expects monic degree-3 polynomial');
  }
  if (_poly_degree(H2) !== 2 || !field.eq(_poly_coeff(H2, 2, field), field.one())) {
    throw new Error('Q3 decoder expects monic degree-2 H2');
  }

  const h1 = _poly_coeff(H2, 1, field);
  const h0 = _poly_coeff(H2, 0, field);

  const alpha2 = field.sub(_poly_coeff(Q3, 2, field), h1);
  const alpha1 = field.sub(
    _poly_coeff(Q3, 1, field),
    field.add(h0, field.mul(alpha2, h1))
  );
  const alpha0 = field.sub(
    _poly_coeff(Q3, 0, field),
    field.mul(alpha2, field.add(h0, alpha1))
  );
  return [alpha0, alpha1, alpha2];
}

// py: tools/poly_schedule.py:3549
// Decode `Q_7[α0..α6](x,H2,H4)` given monic (H2,H4).
//
// In paper notation:
//   S1 = H4 + α3
//   S2 = H4 + α2
//   Q7 = A_2[α0,α1, β2=α4, β1=α5, β0=α6](S1,S2,(x,H2))
//
// This is a solver-free coefficient decoder; it mirrors
// `tools/impl/q_decode.py:decode_Q7`.
function _decode_Q7_coeffs_to_alpha_given_H2_H4(Q7, H2, H4, field) {
  Q7 = _poly_trim(Q7, field);
  H2 = _poly_trim(H2, field);
  H4 = _poly_trim(H4, field);
  if (_poly_degree(Q7) !== 7 || !field.eq(_poly_coeff(Q7, 7, field), field.one())) {
    throw new Error('Q7 decoder expects monic degree-7 polynomial');
  }
  if (_poly_degree(H2) !== 2 || !field.eq(_poly_coeff(H2, 2, field), field.one())) {
    throw new Error('Q7 decoder expects monic degree-2 H2');
  }
  if (_poly_degree(H4) !== 4 || !field.eq(_poly_coeff(H4, 4, field), field.one())) {
    throw new Error('Q7 decoder expects monic degree-4 H4');
  }

  const h2_1 = _poly_coeff(H2, 1, field);
  const h2_0 = _poly_coeff(H2, 0, field);

  const h4_3 = _poly_coeff(H4, 3, field);
  const h4_2 = _poly_coeff(H4, 2, field);
  const h4_1 = _poly_coeff(H4, 1, field);
  const h4_0 = _poly_coeff(H4, 0, field);

  // In A2 notation, n = deg(S1) = deg(S2) = 4.
  const n = 4;

  // beta0 (=α6) from [x^{n+2}]Q = beta0 + [x^{n+1}]A1 + [x^{n+2}]A2.
  // Here [x^{n+2}]A2 = 1, and [x^{n+1}]A1 = h2_1 + h4_3 (since alpha3 is constant).
  const beta0 = field.sub(
    field.sub(_poly_coeff(Q7, n + 2, field), field.add(h2_1, h4_3)),
    field.one()
  );

  // High-degree coefficients of A1 and A2 are independent of alpha2/alpha3 and alpha0/alpha1.
  // Use Q_d = A1_{d-1} + beta0*A1_d + A2_d.
  const A1_6 = field.one();
  const A2_6 = field.one();
  const A2_5 = field.add(h2_1, h4_3);

  const A1_5 = field.sub(_poly_coeff(Q7, 6, field), field.add(beta0, A2_6));
  // A1_4 from degree 5 equation: Q5 = A1_4 + beta0*A1_5 + A2_5.
  const A1_4 = field.sub(
    _poly_coeff(Q7, 5, field),
    field.add(field.mul(beta0, A1_5), A2_5)
  );
  const beta1 = field.sub(
    A1_4,
    field.add(h2_0, field.add(field.mul(h2_1, h4_3), h4_2))
  );

  // A1_3 depends only on known H2/H4 and beta1.
  const A1_3 = field.add(
    h4_1,
    field.add(field.mul(h2_1, h4_2), field.mul(field.add(h2_0, beta1), h4_3))
  );
  // Degree 4 equation: Q4 = A1_3 + beta0*A1_4 + A2_4.
  const A2_4 = field.sub(
    _poly_coeff(Q7, 4, field),
    field.add(A1_3, field.mul(beta0, A1_4))
  );
  const beta2 = field.sub(
    A2_4,
    field.add(h2_0, field.add(field.mul(h2_1, h4_3), h4_2))
  );

  // A2_3 depends only on known H2/H4 and beta2.
  const A2_3 = field.add(
    h4_1,
    field.add(field.mul(h2_1, h4_2), field.mul(field.add(h2_0, beta2), h4_3))
  );
  // Degree 3 equation: Q3 = A1_2 + beta0*A1_3 + A2_3.
  const A1_2 = field.sub(
    _poly_coeff(Q7, 3, field),
    field.add(field.mul(beta0, A1_3), A2_3)
  );
  const base_A1_2 = field.add(
    h4_0,
    field.add(field.mul(h2_1, h4_1), field.mul(field.add(h2_0, beta1), h4_2))
  );
  const alpha3 = field.sub(A1_2, base_A1_2);

  // A1_1 = [x^1]((H2+beta1)*(H4+alpha3)), alpha1 doesn't contribute.
  const base_A1_1 = field.add(
    field.mul(h2_1, h4_0),
    field.mul(field.add(h2_0, beta1), h4_1)
  );
  const A1_1 = field.add(base_A1_1, field.mul(alpha3, h2_1));
  // Degree 2 equation: Q2 = A1_1 + beta0*A1_2 + A2_2.
  const A2_2 = field.sub(
    _poly_coeff(Q7, 2, field),
    field.add(A1_1, field.mul(beta0, A1_2))
  );
  const base_A2_2 = field.add(
    h4_0,
    field.add(field.mul(h2_1, h4_1), field.mul(field.add(h2_0, beta2), h4_2))
  );
  const alpha2 = field.sub(A2_2, base_A2_2);

  // A2_1 = [x^1]((H2+beta2)*(H4+alpha2)), alpha0 doesn't contribute.
  const base_A2_1 = field.add(
    field.mul(h2_1, h4_0),
    field.mul(field.add(h2_0, beta2), h4_1)
  );
  const A2_1 = field.add(base_A2_1, field.mul(alpha2, h2_1));

  // Degree 1 equation: Q1 = A1_0 + beta0*A1_1 + A2_1, where A1_0 includes alpha1.
  const A1_0 = field.sub(
    _poly_coeff(Q7, 1, field),
    field.add(field.mul(beta0, A1_1), A2_1)
  );
  const base_A1_0 = field.mul(field.add(h2_0, beta1), field.add(h4_0, alpha3));
  const alpha1 = field.sub(A1_0, base_A1_0);

  // Degree 0 equation: Q0 = beta0*A1_0 + A2_0, where A2_0 includes alpha0.
  const A2_0 = field.sub(_poly_coeff(Q7, 0, field), field.mul(beta0, A1_0));
  const base_A2_0 = field.mul(field.add(h2_0, beta2), field.add(h4_0, alpha2));
  const alpha0 = field.sub(A2_0, base_A2_0);

  // Map (beta0,beta1,beta2) to (α6,α5,α4).
  return [alpha0, alpha1, alpha2, alpha3, beta2, beta1, beta0];
}

// py: tools/poly_schedule.py:5838
// Decode `Q_{2^k-1}` (Algorithm `alg:constr-known-2n-1`) to its α-parameters.
//
// Constructive (paper-faithful) decoder following Algorithm `alg:decode-Q-2kminus1`.
function _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q, k, Hs, field }) {
  Q = _poly_trim(Q, field);
  if (
    _poly_degree(Q) !== (1 << k) - 1 ||
    !field.eq(_poly_coeff(Q, (1 << k) - 1, field), field.one())
  ) {
    throw new Error('Q decoder expects monic degree (2^k-1)');
  }
  if (Hs.length < k) {
    throw new Error('Q decoder expects Hs=[x,H2,...,H_{2^{k-1}}]');
  }

  if (PEELED_Q && k >= 3) {
    // Q = (H_{2^{k-1}} + gamma) * W + B: divide by the known monic H
    // (quotient = W since deg(gamma*W + B) < deg H), read gamma at the
    // residual's top row (W and B are monic), subtract.
    const m = (1 << (k - 1)) - 1;
    const [W, R] = _poly_divmod_monic(Q, Hs[k - 1], field);
    if (_poly_degree(W) !== m || !field.eq(_poly_coeff(W, m, field), field.one())) {
      throw new Error('peeled Q decoder: quotient is not monic of the right degree');
    }
    const gamma = field.sub(_poly_coeff(R, m, field), field.one());
    const B = _poly_sub(R, _poly_scale_const(W, gamma, field), field);
    return [gamma]
      .concat(
        _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
          Q: W,
          k: k - 1,
          Hs: Hs.slice(0, k - 1),
          field,
        })
      )
      .concat(
        _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
          Q: B,
          k: k - 1,
          Hs: Hs.slice(0, k - 1),
          field,
        })
      );
  }

  const x = Hs[0];
  if (k === 1) {
    // Q_1 = x + α0.
    if (_poly_degree(Q) !== 1) {
      throw new Error('Q1 must have degree 1');
    }
    return [field.sub(_poly_coeff(Q, 0, field), _poly_coeff(x, 0, field))];
  }
  if (k === 2) {
    return _decode_Q3_coeffs_to_alpha_given_H2(Q, Hs[1], field);
  }
  if (k === 3) {
    return _decode_Q7_coeffs_to_alpha_given_H2_H4(Q, Hs[1], Hs[2], field);
  }
  if (k < 4) {
    throw new Error('unreachable');
  }

  // k >= 4: by Lemma `lem:Q-unitriangular` the coefficient map of `Q_{2^k-1}`
  // is unitriangular from high to low degree in the encoder's own parameter
  // order: coeff_j = alpha_j + f_j(alpha_{j+1}, ..., alpha_{2^k-2}).  Solve by
  // descending back-substitution, re-encoding to evaluate each f_j.
  const q = (1 << k) - 1;
  const alpha = [];
  for (let i = 0; i < q; i++) alpha.push(field.zero());
  for (let j = q - 1; j >= 0; j--) {
    const cur = _poly_paper_Q_known_powers({ k, alpha, Hs, field });
    alpha[j] = field.sub(_poly_coeff(Q, j, field), _poly_coeff(cur, j, field));
  }

  const chk = _poly_paper_Q_known_powers({ k, alpha, Hs, field });
  if (!_poly_eq(chk, Q, field)) {
    throw new Error(
      'Q_{2^k-1} decode failed verification (input is not a Q instance for these powers)'
    );
  }
  return alpha;
}

// ====================================================================
// BEGIN g5_decode_P.frag.js
// ====================================================================
// =============================================================================
// g5_decode_P.frag.js — P coefficient decoders for the paper family P_n[α]:
// bases P3/P5/P7, the 4k+1 family, specials P11/P15, and the dispatch
// _decode_P_coeffs_to_paper_params.
// Fragment: function declarations only; runtime (Field, _poly_* helpers) and
// other groups (_decode_square_gadget, _decode_R_k, _decode_Q5_coeffs_to_alpha_given_H2,
// _decode_Q_power_of_2_minus_1_coeffs_to_alpha, _poly_paper_P_from_params) are
// supplied by sibling fragments at assembly time.
// =============================================================================

// py: tools/poly_schedule.py:3212
function _decode_P3_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (coeffs.length !== 4 || !field.eq(coeffs[coeffs.length - 1], field.one())) {
    throw new Error("P3 decoder expects monic degree-3 polynomial coeffs [a0..a2,1]");
  }
  const a0 = coeffs[0], a1 = coeffs[1], a2 = coeffs[2];
  const alpha2 = field.sub(a2, field.one());
  const alpha1 = field.sub(a1, alpha2);
  const alpha0 = field.sub(a0, alpha1);
  return [alpha0, alpha1, alpha2];
}

// py: tools/poly_schedule.py:3223
function _decode_P7_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (coeffs.length !== 8 || !field.eq(coeffs[coeffs.length - 1], field.one())) {
    throw new Error("P7 decoder expects monic degree-7 polynomial coeffs [a0..a6,1]");
  }

  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error("P7 decoding for char(F)=2 is not implemented");
  }
  const inv2 = field.inv(two);

  const [c0, c1, c2, c3, c4, c5, c6] = [coeffs[0], coeffs[1], coeffs[2], coeffs[3], coeffs[4], coeffs[5], coeffs[6]];

  const z2 = field.mul(c6, inv2);
  const z2_sq = field.mul(z2, z2);

  const z1 = field.mul(field.sub(field.sub(c5, z2_sq), field.one()), inv2);
  const z1_sq = field.mul(z1, z1);

  const v4 = field.sub(c4, field.one());
  const two_z2z1 = field.add(field.mul(z2, z1), field.mul(z2, z1));
  const RHS1 = field.sub(field.sub(field.sub(v4, two_z2z1), z2), field.zero());

  const v3 = field.sub(c3, z2);
  const alpha1 = field.sub(field.sub(field.sub(v3, field.mul(z2, RHS1)), z1_sq), z1);

  const v2 = field.sub(field.sub(c2, z1), field.one());
  const W1 = field.sub(field.sub(v2, field.mul(z2, alpha1)), field.mul(z1, RHS1));

  // alpha6 = c1 - (z1+1)*alpha1 - W1*(RHS1 + 1 - W1)
  const z1_plus_1 = field.add(z1, field.one());
  const term1 = field.mul(z1_plus_1, alpha1);
  const term2 = field.mul(W1, field.sub(field.add(RHS1, field.one()), W1));
  const alpha6 = field.sub(field.sub(c1, term1), term2);

  const alpha4 = field.sub(field.sub(z2, field.one()), alpha6);
  const alpha5 = field.sub(z1, field.mul(alpha4, field.add(field.one(), alpha6)));
  const z0 = field.mul(alpha4, alpha5);
  const alpha3 = field.sub(W1, z0);
  const alpha2 = field.sub(field.sub(RHS1, field.add(z0, z0)), alpha3);
  const alpha0 = field.sub(c0, field.mul(field.add(z0, alpha2), alpha1));

  return [alpha0, alpha1, alpha2, alpha3, alpha4, alpha5, alpha6];
}

// py: tools/poly_schedule.py:3267
// Decode the paper base construction for `P_5[α0..α4]` implemented by `_paper_P5`:
//
//   P5[α0..α4](x) = (x + α2) * ( (x^2 + α4) * (x^2 + x + α3) + α1 ) + α0
//
// This decoder is solver-free and works in any characteristic.
function _decode_P5_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (coeffs.length !== 6 || !field.eq(coeffs[coeffs.length - 1], field.one())) {
    throw new Error("P5 decoder expects monic degree-5 polynomial coeffs [a0..a4,1]");
  }

  const [a0, a1, a2, a3, a4] = [coeffs[0], coeffs[1], coeffs[2], coeffs[3], coeffs[4]];

  const alpha2 = field.sub(a4, field.one());
  const alpha2_sq = field.mul(alpha2, alpha2);
  const alpha4 = field.add(field.sub(a2, field.mul(alpha2, a3)), alpha2_sq);
  const alpha3 = field.sub(field.sub(a3, alpha2), alpha4);
  const alpha4_sq = field.mul(alpha4, alpha4);
  const alpha1 = field.add(field.sub(a1, field.mul(alpha4, a3)), alpha4_sq);
  const alpha0 = field.add(field.sub(a0, field.mul(alpha2, a1)), field.mul(alpha2_sq, alpha4));
  return [alpha0, alpha1, alpha2, alpha3, alpha4];
}

// py: tools/poly_schedule.py:3409
// Decode `P_{4k+1}[α0..α_{4k}]` (the main `4k+1` splittable family) for any `k>=2`.
//
// Paper structure (sections/constructions.tex, “4k+1 is splittable”):
//   - H2 = (x + α_{4k})x + α_{4k-1} = x^2 + u*x + v, with (u,v) at the *end*.
//   - \tilde H2 = H2 + α_{4k-2}.
//   - The first `4k-2` parameters are exactly the internal `T_{2k,2}` block.
//   - P = x*T^{(1)}_{2k,2} + T^{(2)}_{2k,2}.
//
// Decoder outline:
//   1) Recover (u,v,\tilde shift) from the top three coefficients (independent of the T-block).
//   2) Form the remainder polynomial P_R = P - (x*H2^{2k} + \tilde H2^{2k}).
//   3) Decode the T-block via `_decode_R_k(k=2k,l=1,...)`.
function _decode_P_4k_plus_1_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (_poly_degree(coeffs) < 0 || !field.eq(_poly_coeff(coeffs, _poly_degree(coeffs), field), field.one())) {
    throw new Error("P_{4k+1} decoder expects a monic polynomial");
  }

  const n = _poly_degree(coeffs);
  if (n < 9 || (n % 4) !== 1) {
    throw new Error(`expected n=4k+1 with k>=2, got n=${n}`);
  }
  const k = Math.floor((n - 1) / 4);

  const two_k = field.coerce(2 * k);
  if (field.is_zero(two_k)) {
    throw new Error("4k+1 decoding requires (2k) invertible in the field");
  }
  const inv_two_k = field.inv(two_k);

  const c_n_minus_1 = _poly_coeff(coeffs, n - 1, field);
  const c_n_minus_2 = _poly_coeff(coeffs, n - 2, field);
  const c_n_minus_3 = _poly_coeff(coeffs, n - 3, field);

  // u from: [x^{4k}]P = 2k*u + 1.
  const u = field.mul(field.sub(c_n_minus_1, field.one()), inv_two_k);

  // v from: [x^{4k-1}]P = C(2k,2)u^2 + 2k*v + 2k*u - k.
  const u2 = field.mul(u, u);
  const choose2 = (2 * k) * (2 * k - 1) / 2; // math.comb(2*k, 2), exact integer
  const term_choose2_u2 = _field_mul_int(field, u2, choose2);
  const num_v = field.add(
    field.sub(field.sub(c_n_minus_2, term_choose2_u2), _field_mul_int(field, u, 2 * k)),
    field.coerce(k),
  );
  const v = field.mul(num_v, inv_two_k);

  // Remaining outer pivots (paper `lem:4k+1-splittable` pivot table):
  //   coeff 4k-2 -> a   (= alpha_{4k-3}, slope -2k)
  //   coeff 4k-3 -> e   (= alpha_{4k-4}, slope  k)
  //   coeff 4k-4 -> rho (= alpha_{4k-2}, slope  k)
  // The parameter-free boundary contributions of the remainder pair
  // (`lem:Rk2l-top-boundary`) are captured by synthetically re-encoding the
  // partial parameter vector, so each pivot is an exact affine solve.
  const partial = new Array(n).fill(field.zero());
  partial[n - 1] = u;
  partial[n - 2] = v;

  for (const [idx, row] of [[n - 4, n - 3], [n - 5, n - 4], [n - 3, n - 5]]) {
    const base_enc = _poly_paper_P_from_params({ params: partial, field: field });
    const probe = partial.slice();
    probe[idx] = field.add(probe[idx], field.one());
    const probe_enc = _poly_paper_P_from_params({ params: probe, field: field });
    const slope = field.sub(_poly_coeff(probe_enc, row, field), _poly_coeff(base_enc, row, field));
    if (field.is_zero(slope)) {
      throw new Error("P_{4k+1} decoder: zero pivot slope (field not admissible?)");
    }
    partial[idx] = field.div(
      field.sub(_poly_coeff(coeffs, row, field), _poly_coeff(base_enc, row, field)), slope
    );
  }
  const tilde_shift = partial[n - 3];

  const x = [field.zero(), field.one()];
  const H2 = [field.coerce(v), field.coerce(u), field.one()];
  const tilde_H2 = _poly_add_const(H2, tilde_shift, field);

  const H_pow = _poly_pow(H2, 2 * k, field);
  const Ht_pow = _poly_pow(_poly_trim(tilde_H2, field), 2 * k, field);
  const known = _poly_add(_poly_shift_xk(H_pow, 1, field), Ht_pow, field);
  const P_R = _poly_sub(coeffs, known, field);

  const [t_params, _Hs_out, _tilde_out] = _decode_R_k({
    k: 2 * k, l: 1, P_R: P_R, Hs: [x, H2], tilde_H_2l: tilde_H2, field: field,
  });
  if (t_params.length !== n - 3) {
    throw new Error("internal error: T_{2k,2} parameter block length mismatch");
  }

  const alpha = t_params.slice().concat([tilde_shift, v, u]);

  const chk = _poly_trim(_poly_paper_P_from_params({ params: alpha, field: field }), field);
  if (!_poly_eq(chk, coeffs, field)) {
    throw new Error("4k+1 decoder produced parameters that do not reproduce the input polynomial");
  }
  return alpha;
}

// py: tools/poly_schedule.py:6087
// Decode `P_11[α0..α10]` (the k=1 instance of the 8k+3 induction).
//
// For k=1 the “compatibility” recovery step collapses to a genuine square-gadget
// because the inner splittable pair is `n=3`, where
//   (S1_1,S1_2) = (H2, H2+α2).
function _decode_P11_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (_poly_degree(coeffs) !== 11 || !field.eq(_poly_coeff(coeffs, 11, field), field.one())) {
    throw new Error("P11 decoder expects a monic degree-11 polynomial");
  }

  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error("P11 decoding requires char(F) != 2");
  }

  // Step 1: decode S2=Q5 and a=α5 from the outer square gadget at d=5.
  // The error term contributes degree-5 coefficient -1 (from -x*(S1_1)^2, with S1_1 monic degree 2).
  const [S2, a] = _decode_square_gadget({
    G: coeffs,
    field: field,
    boundary_error_coeff_deg_d: field.neg(field.one()),
  });
  if (_poly_degree(S2) !== 5) {
    throw new Error("internal error: expected deg(S2)=5 in P11 decoding");
  }

  // Subtract the square gadget to isolate the residual.
  const xS2_sq = _poly_shift_xk(_poly_square(S2, field), 1, field);
  const S2_plus_a_sq = _poly_square(_poly_add_const(S2, a, field), field);
  const P_rem = _poly_sub(coeffs, _poly_add(xS2_sq, S2_plus_a_sq, field), field);

  // Step 2: recover (S1_1, α2) from Ψ = x(S1_1)^2 + (S1_1+α2)^2.
  //
  // For degrees >= 2, the low-degree term (x*α1 + α0) does not contribute, so:
  //   Ψ_{>=2} = -P_rem_{>=2}.
  let psi = new Array(6).fill(field.zero()); // degree 5 max
  for (let d = 2; d < 6; d++) {
    psi[d] = field.neg(_poly_coeff(P_rem, d, field));
  }
  psi[5] = field.one();
  psi = _poly_trim(psi, field);

  const [S1_1, alpha2] = _decode_square_gadget({ G: psi, field: field, boundary_error_coeff_deg_d: field.zero() });
  if (_poly_degree(S1_1) !== 2) {
    throw new Error("internal error: expected deg(S1_1)=2 in P11 decoding");
  }

  // Step 3: recover α0, α1 from P_rem = -Ψ + x*α1 + α0.
  const psi_full = _poly_add(_poly_shift_xk(_poly_square(S1_1, field), 1, field), _poly_square(_poly_add_const(S1_1, alpha2, field), field), field);
  const resid = _poly_add(P_rem, psi_full, field);
  const alpha0 = _poly_coeff(resid, 0, field);
  const alpha1 = _poly_coeff(resid, 1, field);

  // Step 4: recover the embedded `n=3` block parameters α3,α4 from S1_1 (=H2).
  // Here H2 = x^2 + α4 x + α3.
  const alpha4 = _poly_coeff(S1_1, 1, field);
  const alpha3 = _poly_coeff(S1_1, 0, field);

  // Step 5: decode the `Q5` parameter block α6..α10 given H2.
  const q_params = _decode_Q5_coeffs_to_alpha_given_H2(S2, S1_1, field);
  if (q_params.length !== 5) {
    throw new Error("internal error: expected 5 params from Q5 decoder");
  }

  // Global α layout for n=11 (k=1) per `_paper_splittable_pair`:
  //   α0           : scalar in the final T2
  //   α1           : S3 constant
  //   α2..α4       : P3 block
  //   α5           : square-gadget shift on S2
  //   α6..α10      : Q5 block
  const alpha = new Array(11).fill(field.zero());
  alpha[0] = alpha0;
  alpha[1] = alpha1;
  alpha[2] = alpha2;
  alpha[3] = alpha3;
  alpha[4] = alpha4;
  alpha[5] = a;
  for (let i = 0; i < 5; i++) {
    alpha[6 + i] = q_params[i];
  }
  return alpha;
}

// py: tools/poly_schedule.py:6167
// Decode `P_15[α0..α14]` induced by this file’s special-case `n=15` splittable pair.
//
// Structure (from `_paper_splittable_pair(n=15)`):
//   - H2 = x^2 + α7 x + α6
//   - H4 = H2^2 - (x+α5)^2 + α4
//   - S  = Q_7[α8..α14](x,H2,H4)     (paper `Q_known_powers(k=3)`)
//   - T1 = S^2 - (H2+α3)^2 + α1
//   - H8 = H4^2 - (H2+α2)^2 + α0
//   - P  = (x+1)*T1 + H8
//
// This decoder is solver-free and uses coefficient algebra + monic square roots.
// Requires char(F) != 2 (and 4 invertible).
function _decode_P15_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (_poly_degree(coeffs) !== 15 || !field.eq(_poly_coeff(coeffs, 15, field), field.one())) {
    throw new Error("P15 decoder expects a monic degree-15 polynomial");
  }

  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error("P15 decoding requires char(F) != 2");
  }
  const inv2 = field.inv(two);
  const four = field.add(two, two);
  if (field.is_zero(four)) {
    throw new Error("P15 decoding requires 4 invertible in the field");
  }
  const inv4 = field.inv(four);

  const x = [field.zero(), field.one()];
  const x_plus_1 = [field.one(), field.one()];

  // Step 1: recover S^2 coefficients in degrees 7..14 from the clean high window.
  const S_sq_high = new Array(15).fill(field.zero()); // degree 14 max
  S_sq_high[14] = field.one();
  for (let d = 14; d > 8; d--) { // d=14..9 gives S^2[d-1]
    S_sq_high[d - 1] = field.sub(_poly_coeff(coeffs, d, field), S_sq_high[d]);
  }
  // Degree 8 is still clean (other terms max degree 8 but do not contribute to deg 9+).
  // Degree 7 is obtained from [x^8]P = (S^2[8]+S^2[7]) + [x^8]H4^2, and H4 is monic => [x^8]H4^2 = 1.
  S_sq_high[7] = field.sub(field.sub(_poly_coeff(coeffs, 8, field), field.one()), S_sq_high[8]);

  const S = _monic_sqrt_from_high_square_coeffs(S_sq_high, 7, field);
  if (_poly_degree(S) !== 7 || !field.eq(_poly_coeff(S, 7, field), field.one())) {
    throw new Error("internal error: expected monic degree-7 S in P15 decoding");
  }
  const S_sq = _poly_square(S, field);

  // Step 2: residual R = P - (x+1)*S^2 = H4^2 - (x+1)(H2+α3)^2 - (H2+α2)^2 + (x+1)α1 + α0.
  const R = _poly_sub(coeffs, _poly_mul(S_sq, x_plus_1, field), field);

  // Step 3: recover H4 coefficients from (mostly clean) H4^2 coefficients.
  const H4_sq_8 = _poly_coeff(R, 8, field);
  const H4_sq_7 = _poly_coeff(R, 7, field);
  const H4_sq_6 = _poly_coeff(R, 6, field);
  // Degree 5: subtract the known contribution from -x*(H2+α3)^2, which is -1 at degree 5.
  const H4_sq_5 = field.add(_poly_coeff(R, 5, field), field.one());

  if (!field.eq(H4_sq_8, field.one())) {
    throw new Error("internal error: expected monic H4^2 at degree 8 in P15 decoding");
  }

  // Let H4 = x^4 + A x^3 + B x^2 + C x + D.
  // Then H4^2 has:
  //   [x^7]=2A, [x^6]=A^2+2B, [x^5]=2AB+2C, [x^4]=B^2+2AC+2D.
  const A = field.mul(H4_sq_7, inv2);
  // A = 2*α7 (since H4[3] = 2*α7).
  const alpha7 = field.mul(A, inv2);

  const A2 = field.mul(A, A);
  const B = field.mul(field.sub(H4_sq_6, A2), inv2);
  const twoAB = field.add(field.mul(A, B), field.mul(A, B));
  const C = field.mul(field.sub(H4_sq_5, twoAB), inv2);

  // Degree 4: R_4 = (H4^2)_4 - ((H2+α3)^2)_3 - 2, and ((H2+α3)^2)_3 = 2*α7 (independent of α3).
  const H4_sq_4 = field.add(_poly_coeff(R, 4, field), field.add(_field_mul_int(field, alpha7, 2), field.coerce(2)));
  const B2 = field.mul(B, B);
  const twoAC = _field_mul_int(field, field.mul(A, C), 2);
  const D = field.mul(field.sub(field.sub(H4_sq_4, B2), twoAC), inv2);

  const H4 = _poly_trim([D, C, B, A, field.one()], field);
  if (_poly_degree(H4) !== 4 || !field.eq(_poly_coeff(H4, 4, field), field.one())) {
    throw new Error("internal error: expected monic degree-4 H4 in P15 decoding");
  }

  // Step 4: recover H2 params and α4,α5 from H4 = H2^2 - (x+α5)^2 + α4.
  // Here H2 = x^2 + α7 x + α6.
  const alpha6 = field.mul(field.sub(field.add(B, field.one()), field.mul(alpha7, alpha7)), inv2);
  const alpha5 = field.sub(field.mul(alpha7, alpha6), field.mul(C, inv2));
  const alpha4 = field.sub(D, field.sub(field.mul(alpha6, alpha6), field.mul(alpha5, alpha5)));

  const H2 = _poly_trim([alpha6, alpha7, field.one()], field);

  // Step 5: subtract H4^2 and solve the remaining low scalars α0..α3.
  const H4_sq_full = _poly_square(H4, field);
  const R2 = _poly_sub(R, H4_sq_full, field);

  const b = alpha7;
  const c = alpha6;
  // From degree 3:
  //   R2_3 = -((x+1)(H2+α3)^2)_3 - ((H2+α2)^2)_3
  //        = -((H2+α3)^2_3 + (H2+α3)^2_2) - 2b
  // and (H2+α3)^2_2 = b^2 + 2(c+α3).
  const s2_sq_2 = field.sub(field.neg(_poly_coeff(R2, 3, field)), _field_mul_int(field, b, 4));
  const d3 = field.mul(field.sub(s2_sq_2, field.mul(b, b)), inv2); // d3 = c + α3
  const alpha3 = field.sub(d3, c);

  // From degree 2:
  //   R2_2 = -( (H2+α3)^2_2 + (H2+α3)^2_1 ) - (H2+α2)^2_2
  // where (H2+α3)^2_1 = 2*b*d3 and (H2+α2)^2_2 = b^2 + 2*d2.
  const two_b_d3 = _field_mul_int(field, field.mul(b, d3), 2);
  const num_d2 = field.sub(
    field.sub(field.neg(_poly_coeff(R2, 2, field)), field.add(s2_sq_2, two_b_d3)),
    field.mul(b, b),
  );
  const d2 = field.mul(num_d2, inv2); // d2 = c + α2
  const alpha2 = field.sub(d2, c);

  // Degree 1: R2_1 = -(2*b*d3 + d3^2) - (2*b*d2) + α1.
  const alpha1 = field.add(
    _poly_coeff(R2, 1, field),
    field.add(field.add(two_b_d3, field.mul(d3, d3)), _field_mul_int(field, field.mul(b, d2), 2)),
  );

  // Degree 0: R2_0 = -d3^2 - d2^2 + α1 + α0.
  const alpha0 = field.sub(
    field.add(_poly_coeff(R2, 0, field), field.add(field.mul(d3, d3), field.mul(d2, d2))),
    alpha1,
  );

  // Step 6: decode the embedded Q7 block α8..α14 from S given (H2,H4).
  const q_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: S, k: 3, Hs: [x, H2, H4], field: field });
  if (q_params.length !== 7) {
    throw new Error("internal error: expected 7 params from Q7 decoder");
  }

  const alpha = new Array(15).fill(field.zero());
  alpha[0] = alpha0;
  alpha[1] = alpha1;
  alpha[2] = alpha2;
  alpha[3] = alpha3;
  alpha[4] = alpha4;
  alpha[5] = alpha5;
  alpha[6] = alpha6;
  alpha[7] = alpha7;
  for (let i = 0; i < q_params.length; i++) {
    alpha[8 + i] = q_params[i];
  }

  // Sanity: re-encode.
  const chk = _poly_trim(_poly_paper_P_from_params({ params: alpha, field: field }), field);
  if (!_poly_eq(chk, coeffs, field)) {
    throw new Error("P15 decoder produced parameters that do not reproduce the input polynomial");
  }
  return alpha;
}

// py: tools/poly_schedule.py:6606
// Decode a monic polynomial's coefficients into the paper parameters α0..α_{n-1}
// for the family P_n[α] implemented by `compile_paper_params_chain`.
//
// Implemented here:
//   - the bases n = 1,3,5,7 and the specials n = 11, 15;
//   - all even n by the paper's even-lift: P_n = α0 + x * P_{n-1}(α1..);
//   - the main splittable family n ≡ 1 (mod 4) (lem:4k+1-splittable +
//     alg:decode-Rk2l via `_decode_R_k`).
//
// The remaining odd families (8k+3, 8k+7, and the specials 27/31) are
// implemented in `tools/polychain.py` on top of the primitives in this file.
function _decode_P_coeffs_to_paper_params(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (coeffs.length <= 1) {
    throw new Error("polynomial must have positive degree for paper decoding");
  }
  if (!field.eq(coeffs[coeffs.length - 1], field.one())) {
    throw new Error("paper decoding requires a monic polynomial (leading coefficient 1)");
  }

  const n = coeffs.length - 1;
  if (n === 1) {
    return [coeffs[0]];
  }

  if ((n % 2) === 0) {
    // P_n = α0 + x * P_{n-1}(α1..)
    const alpha0 = coeffs[0];
    const rest = _decode_P_coeffs_to_paper_params(coeffs.slice(1), field);
    return [alpha0].concat(rest);
  }

  if (n === 3) {
    return _decode_P3_coeffs_to_alpha(coeffs, field);
  }
  if (n === 5) {
    return _decode_P5_coeffs_to_alpha(coeffs, field);
  }
  if (n === 7) {
    return _decode_P7_coeffs_to_alpha(coeffs, field);
  }
  if (n === 11) {
    return _decode_P11_coeffs_to_alpha(coeffs, field);
  }
  if (n === 15) {
    return _decode_P15_coeffs_to_alpha(coeffs, field);
  }

  // Main splittable family: n = 4k+1, k>=2.
  if ((n % 4) === 1 && n >= 9) {
    return _decode_P_4k_plus_1_coeffs_to_alpha(coeffs, field);
  }

  // py: the peeling fallback is intentionally not ported because the branch is dead.
  throw new Error('peeling fallback not ported');
}

// ====================================================================
// BEGIN g6_decode_Rk.frag.js
// ====================================================================
// g6_decode_Rk.frag.js — R_k remainder decoders (paper alg:decode-Rk2l).
// Fragment: function declarations only; assembled into core.js after
// runtime.frag.js.  Cross-group callees (supplied by other fragments):
//   _poly_paper_T, _poly_remainder_poly_from_T                      (g3)
//   _recover_monic_factor_high_coeffs_from_product (returns a
//     Map<number, field element>, mirror of Python Dict[int, Number]),
//   _scalar_shift_from_square_boundary, _decode_by_descending_pivots,
//   _decode_Q_power_of_2_minus_1_coeffs_to_alpha                    (g4)

// JS-only private helper standing in for Python's math.comb (exact for the
// small arguments used here: r <= 5, products well below 2^53).
function _g6_math_comb(n, r) {
  if (r < 0 || n < 0 || r > n) return 0;
  let res = 1;
  for (let i = 0; i < r; i++) {
    // res == C(n, i), so res * (n - i) is divisible by (i + 1): exact.
    res = (res * (n - i)) / (i + 1);
  }
  return res;
}

// py: tools/poly_schedule.py:4541
// Decode the remainder polynomial `P_R = x R^{(1)}_{k,2^l} + R^{(2)}_{k,2^l}`.
//
// Returns:
//   [alpha_block, Hs_out, tilde_out]
//
// This is a coefficient-level port of the paper-shaped peeling decoders in
// `tools/impl/splittable_decode.py`, but restricted (for now) to the even-k
// branch. Odd-k decoding is not implemented yet.
function _decode_R_k({ k, l, P_R, Hs, tilde_H_2l, field }) {
  if (k < 1) throw new Error('k must be >= 1');
  if (l < 1) throw new Error('l must be >= 1');
  if (Hs.length <= l) throw new Error('Hs must include H_{2^l} at index l');

  if (k === 1) return [[], Hs.slice(), _poly_trim(tilde_H_2l, field)];
  if (k % 2 !== 0) {
    return _decode_R_odd_k({ k, l, P_R, Hs, tilde_H_2l, field });
  }

  return _decode_R_even_k({ k, l, P_R, Hs, tilde_H_2l, field });
}

// py: tools/poly_schedule.py:4576
// Even-k branch of `_decode_R_k` (paper Algorithm `alg:decode-Rk2l` / Lemma R_{k,2^l}).
//
// Handles both the shared l==1 base (`alg:constr-Tk2l-base`) and l>=2.
function _decode_R_even_k({ k, l, P_R, Hs, tilde_H_2l, field }) {
  if (k < 2 || k % 2 !== 0) throw new Error('decode_R_even_k expects even k>=2');

  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) throw new Error('R-decoding requires char(F) != 2');
  const inv2 = field.inv(two);

  if (l === 1) {
    // Shared even-k l==1 base (`alg:constr-Tk2l-base`):
    //   H4 = H2^2 - (x + a1)^2 + a0,   tilde_H4 = H4 + (tilde_H2 - H2).
    // The two tail scalars are descending affine pivots of P_R at degrees
    // 2k-2 and 2k-3; at degree 2k-3 the inner remainder contributes only
    // through its constant leading coefficient (`lem:Rk2l-leading-coeff`),
    // so probing the tail-only remainder encoder yields exact pivot data.
    P_R = _poly_trim(P_R, field);
    const H2 = _poly_trim(Hs[1], field);
    const tilde_H2 = _poly_trim(tilde_H_2l, field);
    if (_poly_degree(H2) !== 2 || !field.eq(_poly_coeff(H2, 2, field), field.one())) {
      throw new Error('expected monic degree-2 H2 for l==1 remainder decoder');
    }
    if (_poly_degree(tilde_H2) !== 2 || !field.eq(_poly_coeff(tilde_H2, 2, field), field.one())) {
      throw new Error('expected monic degree-2 tilde_H2 for l==1 remainder decoder');
    }
    const delta = _poly_trim(_poly_sub(tilde_H2, H2, field), field);
    if (_poly_degree(delta) > 0) {
      throw new Error('the shared l==1 base requires tilde_H2 - H2 to be a scalar');
    }

    const m_int = Math.floor(k / 2);
    const total = (k - 1) * 2;
    const x = [field.zero(), field.one()];

    function _tail_remainder(a0, a1) {
      const al = new Array(total).fill(field.zero());
      al[total - 2] = a0;
      al[total - 1] = a1;
      return _poly_remainder_poly_from_T({ k, l: 1, alpha: al, Hs, tilde_H_2l: tilde_H2, field });
    }

    const tail_vals = [field.zero(), field.zero()]; // (a0, a1)
    for (const [idx, row] of [[1, 2 * k - 2], [0, 2 * k - 3]]) {
      const base = _tail_remainder(tail_vals[0], tail_vals[1]);
      const probe_vals = tail_vals.slice();
      probe_vals[idx] = field.add(probe_vals[idx], field.one());
      const probe = _tail_remainder(probe_vals[0], probe_vals[1]);
      const slope = field.sub(_poly_coeff(probe, row, field), _poly_coeff(base, row, field));
      if (field.is_zero(slope)) {
        throw new Error('l==1 even decoder: zero pivot slope (field not admissible?)');
      }
      tail_vals[idx] = field.div(
        field.sub(_poly_coeff(P_R, row, field), _poly_coeff(base, row, field)), slope
      );
    }
    const alpha_const = tail_vals[0], alpha_shift = tail_vals[1];

    // Build (H4, tilde_H4) and isolate the inner remainder exactly.
    const x_plus = _poly_add_const(x, alpha_shift, field);
    const H4 = _poly_add(_poly_sub(_poly_square(H2, field), _poly_square(x_plus, field), field), [alpha_const], field);
    const tilde_H4 = _poly_trim(_poly_add(H4, delta, field), field);

    const base_poly = _poly_add(
      _poly_shift_xk(_poly_sub(_poly_pow(H4, m_int, field), _poly_pow(H2, k, field), field), 1, field),
      _poly_sub(_poly_pow(tilde_H4, m_int, field), _poly_pow(tilde_H2, k, field), field),
      field
    );
    const P_inner = _poly_sub(P_R, base_poly, field);

    let inner_alphas = [];
    let Hs_out = [Hs[0], H2, _poly_trim(H4, field)];
    let tilde_out = tilde_H4;
    if (m_int > 1) {
      [inner_alphas, Hs_out, tilde_out] = _decode_R_k({
        k: m_int, l: 2, P_R: P_inner, Hs: [Hs[0], H2, _poly_trim(H4, field)], tilde_H_2l: tilde_H4, field,
      });
    }

    const full = inner_alphas.concat([alpha_const, alpha_shift]);
    if (full.length !== total) {
      throw new Error('internal: decoded alpha count mismatch (l==1 even decoder)');
    }
    return [full, Hs_out, tilde_out];
  }

  // l>=2 branch
  const D = 1 << l;
  const total = (k - 1) * D;
  const d = (k - 2) * D;
  const m = Math.floor(k / 2);
  const inv_m = field.inv(field.coerce(m));

  P_R = _poly_trim(P_R, field);
  const H = _poly_trim(Hs[l], field);
  const H_half = _poly_trim(Hs[l - 1], field);
  tilde_H_2l = _poly_trim(tilde_H_2l, field);

  const H_pow = _poly_pow(H, k - 2, field);
  const Ht_pow = _poly_pow(tilde_H_2l, k - 2, field);

  // Stage 1: recover S1_1 from the top window (> d + D/2) by peeling the monic factor.
  const known_tilde_top = _poly_scale_int(_poly_mul(_poly_square(H_half, field), Ht_pow, field), -1, field);

  const max_prod_deg = d + D;
  const prod = new Array(max_prod_deg + 1).fill(field.zero());
  for (let u_deg = D; u_deg >= Math.floor(D / 2); u_deg--) {
    const p_deg = d + u_deg;
    const pr_deg = p_deg + 1;
    const rhs = field.sub(field.mul(_poly_coeff(P_R, pr_deg, field), inv_m), _poly_coeff(known_tilde_top, pr_deg, field));
    prod[p_deg] = field.neg(rhs);
  }

  const S1_1_sq_high = _recover_monic_factor_high_coeffs_from_product({
    product: prod,
    known_factor: H_pow,
    factor_deg: D,
    min_deg: Math.floor(D / 2),
    field,
  });
  const S1_1_sq_poly = new Array(D + 1).fill(field.zero());
  for (const [deg_i, coeff_i] of S1_1_sq_high) {
    S1_1_sq_poly[deg_i] = field.coerce(coeff_i);
  }
  S1_1_sq_poly[D] = field.one();
  const S1_1 = _monic_sqrt_from_high_square_coeffs(S1_1_sq_poly, Math.floor(D / 2), field);

  // Decode the embedded Q_{2^{l-1}-1} block in S1_1: Q_hi = S1_1 - H_half.
  const Q_hi = _poly_sub(S1_1, H_half, field);
  const k_q = l - 1;
  const q_hi_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: Q_hi, k: k_q, Hs: Hs.slice(0, l - 1), field });

  // Stage 1.5: recover scalar shift s in S2_1 = H_half + s from the boundary degree.
  const target_deg = d + Math.floor(D / 2);
  const C_tdeg = field.mul(_poly_coeff(P_R, target_deg, field), inv_m);
  const x_neg_s1_sq_hpow = _poly_shift_xk(
    _poly_scale_int(_poly_mul(_poly_square(S1_1, field), H_pow, field), -1, field), 1, field
  );
  const tilde_base = _poly_coeff(known_tilde_top, target_deg, field);
  const s2_1_shift = field.mul(field.sub(field.add(field.add(_poly_coeff(x_neg_s1_sq_hpow, target_deg, field), field.one()), tilde_base), C_tdeg), inv2);
  const S2_1 = _poly_add_const(H_half, s2_1_shift, field);
  const tilde_term = _poly_scale_int(_poly_mul(_poly_square(S2_1, field), Ht_pow, field), -1, field);

  // Stage 2: recover S1_2 coefficients in degrees >= 1 via monic-factor peeling.
  const factor_deg = Math.floor(D / 2) - 1;
  const prod2 = new Array(d + Math.floor(D / 2) + 1).fill(field.zero());
  for (let u_deg = Math.floor(D / 2) - 1; u_deg >= 1; u_deg--) {
    const pr_deg = d + u_deg + 1;
    if (pr_deg <= d + 1) continue;
    const C_pr = field.mul(_poly_coeff(P_R, pr_deg, field), inv_m);
    const known = field.add(_poly_coeff(x_neg_s1_sq_hpow, pr_deg, field), _poly_coeff(tilde_term, pr_deg, field));
    const rhs = field.sub(C_pr, known);
    prod2[pr_deg - 1] = rhs;
  }

  const S1_2_high = _recover_monic_factor_high_coeffs_from_product({
    product: prod2,
    known_factor: H_pow,
    factor_deg,
    min_deg: 1,
    field,
  });
  let S1_2_no_const = new Array(factor_deg + 1).fill(field.zero());
  for (const [deg_i, coeff_i] of S1_2_high) {
    if (deg_i <= factor_deg) {
      S1_2_no_const[deg_i] = field.coerce(coeff_i);
    }
  }
  S1_2_no_const[0] = field.zero();
  S1_2_no_const = _poly_trim(S1_2_no_const, field);

  // Boundary degrees: solve the constant term of S1_2 and the scalar S2_2.
  //
  // We compute the paper's boundary-error coefficients (e_{d+1}, e_d) using an
  // auxiliary assignment where:
  //   - recursive block is 0 (prefix all zeros),
  //   - S2_2 is 0,
  //   - and S1_2 is any monic polynomial with the recovered high coefficients
  //     and constant term forced to 0 (so it's still a valid Q instance by decodability).
  const q_lo_params_aux = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
    Q: S1_2_no_const, k: k_q, Hs: Hs.slice(0, l - 1), field,
  });
  const tail = new Array(D).fill(field.zero());
  tail[0] = field.zero(); // S2_2 scalar forced to 0
  for (const [i, v] of q_lo_params_aux.entries()) {
    tail[1 + i] = v;
  }
  tail[Math.floor(D / 2)] = s2_1_shift;
  for (const [i, v] of q_hi_params.entries()) {
    tail[Math.floor(D / 2) + 1 + i] = v;
  }

  const alphas_aux = new Array(total).fill(field.zero());
  for (let i = 0; i < D; i++) {
    alphas_aux[d + i] = tail[i];
  }
  const P_aux = _poly_remainder_poly_from_T({ k, l, alpha: alphas_aux, Hs, tilde_H_2l, field });

  const C_aux = _poly_add(
    _poly_shift_xk(_poly_mul(_poly_add(_poly_scale_int(_poly_square(S1_1, field), -1, field), S1_2_no_const, field), H_pow, field), 1, field),
    _poly_mul(_poly_scale_int(_poly_square(S2_1, field), -1, field), Ht_pow, field),
    field
  );
  const E_aux = _poly_sub(P_aux, _poly_scale_int(C_aux, m, field), field);
  const e_d1 = _poly_coeff(E_aux, d + 1, field);
  const e_d0 = _poly_coeff(E_aux, d, field);

  // Solve s1_2_0 from degree d+1.
  const C_d1 = field.mul(field.sub(_poly_coeff(P_R, d + 1, field), e_d1), inv_m);
  const known_d1 = field.add(_poly_coeff(x_neg_s1_sq_hpow, d + 1, field), _poly_coeff(tilde_term, d + 1, field));
  const prod_d = field.sub(C_d1, known_d1); // equals [x^d](S1_2*H_pow)
  const prod_known = _poly_coeff(_poly_mul(S1_2_no_const, H_pow, field), d, field);
  const s1_2_0 = field.sub(prod_d, prod_known);
  const S1_2 = _poly_add_const(S1_2_no_const, s1_2_0, field);

  // Solve S2_2 scalar from degree d.
  const C_d0 = field.mul(field.sub(_poly_coeff(P_R, d, field), e_d0), inv_m);
  const x_s1_2_hpow_d0 = _poly_coeff(_poly_shift_xk(_poly_mul(S1_2, H_pow, field), 1, field), d, field);
  const known_d0 = field.add(field.add(_poly_coeff(x_neg_s1_sq_hpow, d, field), x_s1_2_hpow_d0), _poly_coeff(tilde_term, d, field));
  const s2_2_scalar = field.sub(C_d0, known_d0);

  // Decode q_lo parameters from the fully recovered S1_2.
  const q_lo_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: S1_2, k: k_q, Hs: Hs.slice(0, l - 1), field });

  // Assemble the tail alphas in the exact layout used by `_paper_T` (even case l>=2).
  const tail_out = new Array(D).fill(field.zero());
  tail_out[0] = s2_2_scalar;
  for (const [i, v] of q_lo_params.entries()) {
    tail_out[1 + i] = v;
  }
  tail_out[Math.floor(D / 2)] = s2_1_shift;
  for (const [i, v] of q_hi_params.entries()) {
    tail_out[Math.floor(D / 2) + 1 + i] = v;
  }

  // Build H_{2^{l+1}} and \tilde H_{2^{l+1}} from the decoded tail, using the k=2 instance.
  const [T1_tail, T2_tail, Hs_out_tail, tilde_out_tail] = _poly_paper_T({
    k: 2, l, alpha: tail_out, Hs, tilde_H_2l, field,
  });
  const H_next = _poly_trim(Hs_out_tail[l + 1], field);
  const H_tilde_next = _poly_trim(tilde_out_tail, field);

  // Isolate the prefix remainder polynomial by subtracting the tail-only remainder,
  // then compensate by adding the zero-parameter recursive remainder (boundary correction).
  const tail_only = new Array(total).fill(field.zero());
  for (let i = 0; i < D; i++) {
    tail_only[d + i] = tail_out[i];
  }
  const P_tail = _poly_remainder_poly_from_T({ k, l, alpha: tail_only, Hs, tilde_H_2l, field });

  let prefix = [];
  let P_prefix = _poly_sub(P_R, P_tail, field);
  let Hs_out_final, tilde_out_final;
  if (m > 1) {
    const P_inner0 = _poly_remainder_poly_from_T({
      k: m, l: l + 1, alpha: new Array(d).fill(field.zero()), Hs: Hs.concat([H_next]), tilde_H_2l: H_tilde_next, field,
    });
    P_prefix = _poly_add(P_prefix, P_inner0, field);

    const [inner_alpha, Hs_out, tilde_out] = _decode_R_k({
      k: m, l: l + 1, P_R: P_prefix, Hs: Hs.concat([H_next]), tilde_H_2l: H_tilde_next, field,
    });
    if (inner_alpha.length !== d) {
      throw new Error('internal: prefix length mismatch in even-k decoder');
    }
    prefix = inner_alpha;
    Hs_out_final = Hs_out;
    tilde_out_final = tilde_out;
  } else {
    Hs_out_final = Hs.concat([H_next]);
    tilde_out_final = H_tilde_next;
  }

  const alpha_out = prefix.concat(tail_out);
  if (alpha_out.length !== total) {
    throw new Error('internal: decoded alpha count mismatch in even-k decoder');
  }
  return [alpha_out, Hs_out_final, tilde_out_final];
}

// py: tools/poly_schedule.py:4846
// Coefficient helper for the odd-k branch of `R_{k,2^l}` decoding.
//
// Matches `tools/impl/splittable_decode.py:_hatR1_combined_coeff_at_degree` in
// coefficient-list arithmetic:
//
//   \hat R^{(1)}_1 = sum_{i=3}^{k-1} binom(k-1,i) H^{k-i} S1_1^i
//                    - (k-1) sum_{i=2}^{k-1} binom(k-1,i) H^{k-i-1} S1_1^{i+1}
//   \hat R^{(2)}_1 = same with (H_tilde,S2_1)
//
// Returns coeff( x*\hat R^{(1)}_1 + \hat R^{(2)}_1, deg ).
//
// We truncate to i<=4, which suffices for the boundary degrees used by the
// proof/decoder (higher i cannot reach those degrees by degree reasons).
function _hatR1_combined_coeff_at_degree({ k, H, S1_1, H_tilde, S2_1, deg, field }) {
  if (k < 3 || k % 2 === 0) throw new Error('_hatR1 helper requires odd k>=3');
  if (deg < 0) return field.zero();

  H = _poly_trim(H, field);
  S1_1 = _poly_trim(S1_1, field);
  H_tilde = _poly_trim(H_tilde, field);
  S2_1 = _poly_trim(S2_1, field);

  const i_max = Math.min(4, k - 1);

  let hat1 = [field.zero()];
  for (let i = 3; i <= i_max; i++) {
    const term = _poly_mul(_poly_pow(H, k - i, field), _poly_pow(S1_1, i, field), field);
    hat1 = _poly_add(hat1, _poly_scale_int(term, _g6_math_comb(k - 1, i), field), field);
  }
  for (let i = 2; i <= i_max; i++) {
    if (k - i - 1 < 0) continue;
    const term = _poly_mul(_poly_pow(H, k - i - 1, field), _poly_pow(S1_1, i + 1, field), field);
    hat1 = _poly_sub(hat1, _poly_scale_int(term, (k - 1) * _g6_math_comb(k - 1, i), field), field);
  }

  let hat2 = [field.zero()];
  for (let i = 3; i <= i_max; i++) {
    const term = _poly_mul(_poly_pow(H_tilde, k - i, field), _poly_pow(S2_1, i, field), field);
    hat2 = _poly_add(hat2, _poly_scale_int(term, _g6_math_comb(k - 1, i), field), field);
  }
  for (let i = 2; i <= i_max; i++) {
    if (k - i - 1 < 0) continue;
    const term = _poly_mul(_poly_pow(H_tilde, k - i - 1, field), _poly_pow(S2_1, i + 1, field), field);
    hat2 = _poly_sub(hat2, _poly_scale_int(term, (k - 1) * _g6_math_comb(k - 1, i), field), field);
  }

  const combined = _poly_add(_poly_shift_xk(hat1, 1, field), hat2, field);
  return _poly_coeff(combined, deg, field);
}

// py: tools/poly_schedule.py:4908
// Odd-k branch of `_decode_R_k` (paper Algorithm `alg:decode-Rk2l` / Lemma `lem:Rk2l`).
//
// Structure:
//   - `l == 2` (shared-product base, Algorithm `alg:constr-Tk2l-base`, odd
//     branch): the four tail scalars u,v,w,z are recovered from the four
//     descending affine pivots of `P_R` at degrees d-1..d-4 (d = 4(k-1)),
//     whose slopes are -k(k-1), -(k-1), m, m -- the pivot table in the
//     shared-base part of the proof of `lem:Rk2l`.
//   - `l >= 3`: the tail block is recovered by the stage-1/stage-2 window
//     peeling of the proof of `lem:Rk2l` (`lem:peel-monic-factor`,
//     `lem:monic-from-power` with m=2, `lem:scalar-shift-square`).
//   - In both cases the remaining head+mid parameters are then extracted by
//     descending affine pivots of the frozen-tail remainder map
//     (`_decode_by_descending_pivots`); this realizes the Multiplicativity /
//     Additivity certificate steps of `alg:decode-Rk2l` numerically.
function _decode_R_odd_k({ k, l, P_R, Hs, tilde_H_2l, field }) {
  if (k < 3 || k % 2 === 0) throw new Error('decode_R_odd_k expects odd k>=3');
  if (l < 2) throw new Error('odd-k remainder decoding requires l>=2');
  if (Hs.length <= l) throw new Error('Hs must include H_{2^l} at index l');

  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) throw new Error('odd-k remainder decoding requires char(F) != 2');
  const inv2 = field.inv(two);

  const three = field.coerce(3);
  if (field.is_zero(three)) {
    throw new Error('odd-k remainder decoding currently requires char(F) != 3');
  }
  const inv3 = field.inv(three);

  const D = 1 << l;
  const total = (k - 1) * D;
  const k_half = Math.floor((k - 1) / 2);
  const m = field.coerce(k_half);
  if (field.is_zero(m)) {
    throw new Error('odd-k remainder decoding requires (k-1)/2 invertible in the field');
  }
  const inv_m = field.inv(m);

  P_R = _poly_trim(P_R, field);
  const H = _poly_trim(Hs[l], field);
  const H_tilde = _poly_trim(tilde_H_2l, field);
  const H_half = _poly_trim(Hs[l - 1], field);
  const H_quarter = _poly_trim(Hs[l - 2], field);

  let tail_out;
  if (l === 2) {
    // Shared-product odd base.  Check the admissibility precondition
    // tilde_H4 - H4 scalar, then run the four tail pivots.
    const rho = _poly_trim(_poly_sub(H_tilde, H, field), field);
    if (_poly_degree(rho) > 0) {
      throw new Error('the shared odd l==2 base requires tilde_H4 - H4 to be a scalar');
    }

    const d = total;
    // Tail layout (alpha[total-4:total]): [z, w, v, u] with
    //   u = alpha_{4k-5} (S1_1 shift), v = alpha_{4k-6} (S1_2 shift),
    //   w = alpha_{4k-7} (S1_3),       z = alpha_{4k-8} (tilde_H8 shift).
    const expected_slopes = { 1: -k * (k - 1), 2: -(k - 1), 3: k_half, 4: k_half };

    function _tail_remainder(vals) {
      const al = new Array(total).fill(field.zero());
      for (const [i, v] of vals.entries()) {
        al[total - 4 + i] = v;
      }
      return _poly_remainder_poly_from_T({ k, l: 2, alpha: al, Hs, tilde_H_2l: H_tilde, field });
    }

    const tail_vals = new Array(4).fill(field.zero());
    for (const j of [1, 2, 3, 4]) {
      const row = d - j;
      const base = _tail_remainder(tail_vals);
      const probe_vals = tail_vals.slice();
      probe_vals[4 - j] = field.add(probe_vals[4 - j], field.one());
      const probe = _tail_remainder(probe_vals);
      const slope = field.sub(_poly_coeff(probe, row, field), _poly_coeff(base, row, field));
      if (field.is_zero(slope)) {
        throw new Error('l==2 odd base: zero pivot slope (field not admissible?)');
      }
      if (!field.eq(slope, field.coerce(expected_slopes[j]))) {
        throw new Error('l==2 odd base: pivot slope does not match the lem:Rk2l table');
      }
      tail_vals[4 - j] = field.div(
        field.sub(_poly_coeff(P_R, row, field), _poly_coeff(base, row, field)), slope
      );
    }
    tail_out = tail_vals.slice();
  } else {
    // Stage 1: recover S1_1 (monic degree D/2).
    const c1 = field.mul(field.mul(field.coerce(k), field.coerce(k - 1)), inv2); // k(k-1)/2
    if (field.is_zero(c1)) {
      throw new Error('odd-k remainder decoding requires k(k-1)/2 invertible in the field');
    }
    const inv_c1 = field.inv(c1);

    const H_pow = _poly_pow(H, k - 2, field);
    const Ht_pow = _poly_pow(H_tilde, k - 2, field);

    const known_R2_top = _poly_mul(_poly_mul(_poly_square(H_half, field), Ht_pow, field), [field.neg(c1)], field);

    const prod1 = new Array((k - 1) * D + 1).fill(field.zero()); // degrees 0..(k-1)D
    const cubic_top = field.mul(field.coerce(k * (k - 1) * (k - 2)), inv3); // k(k-1)(k-2)/3
    for (let d = (k - 1) * D; d >= (k - 2) * D + Math.floor(D / 2); d--) {
      const pr_deg = d + 1;
      let rhs = field.sub(_poly_coeff(P_R, pr_deg, field), _poly_coeff(known_R2_top, pr_deg, field));
      if (d === (k - 2) * D + Math.floor(D / 2)) {
        // Boundary correction: stage-2 contributes -m at this top degree and
        // the x-shifted cubic term contributes -cubic_top.
        rhs = field.add(rhs, field.add(field.coerce(k_half), cubic_top));
      }
      prod1[d] = field.mul(field.neg(rhs), inv_c1);
    }

    const U1_high = _recover_monic_factor_high_coeffs_from_product({
      product: prod1,
      known_factor: H_pow,
      factor_deg: D,
      min_deg: Math.floor(D / 2),
      field,
    });
    const U1_poly = new Array(D + 1).fill(field.zero());
    for (const [deg_i, coeff_i] of U1_high) {
      U1_poly[deg_i] = field.coerce(coeff_i);
    }
    U1_poly[D] = field.one();
    const S1_1 = _monic_sqrt_from_high_square_coeffs(_poly_trim(U1_poly, field), Math.floor(D / 2), field);

    const Q_hi = _poly_sub(S1_1, H_half, field);
    const q_hi_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: Q_hi, k: l - 1, Hs: Hs.slice(0, l - 1), field });

    // Precompute K1 (depends only on H and S1_1).
    const K1 = _poly_mul(
      _poly_sub(H, _poly_scale_int(S1_1, k - 1, field), field),
      _poly_pow(_poly_add(H, S1_1, field), k - 3, field),
      field
    );
    const degK1 = _poly_degree(K1);
    if (degK1 !== (k - 2) * D) {
      throw new Error('internal: unexpected deg(K1) in odd-k decoder');
    }

    // Stage 1.5: recover the scalar shift in S2_1 = H_half + s.
    const deg_shift = (k - 2) * D + Math.floor(D / 2);
    const stage1_x = _poly_shift_xk(
      _poly_mul(_poly_mul(_poly_square(S1_1, field), H_pow, field), [field.neg(c1)], field),
      1,
      field
    );
    const cubic_coeff = field.neg(cubic_top);
    const cubic_x = _poly_shift_xk(
      _poly_mul(_poly_mul(_poly_pow(H, k - 3, field), _poly_pow(S1_1, 3, field), field), [cubic_coeff], field),
      1,
      field
    );

    // Stage-2 contribution at deg_shift uses only the top 2 coefficients of G1 and K1.
    // Leading G1 coefficient is -1; next is -2*a where a = [x^{D/4-1}]S1_2 and
    // S1_2's top-two coefficients are known from H_quarter and monicity.
    const D4 = Math.floor(D / 4);
    const a_s1_2 = field.add(_poly_coeff(H_quarter, D4 - 1, field), field.one());
    const g1k1_deg_shift_minus1 = field.sub(field.neg(_poly_coeff(K1, degK1 - 1, field)), _field_mul_int(field, a_s1_2, 2));
    const stage2_at_deg_shift = field.mul(m, field.sub(g1k1_deg_shift_minus1, field.one()));

    // Also subtract the tilde-side cubic top coefficient at this degree: cubic_coeff.
    let coeff_stage1_tilde_boundary = field.sub(_poly_coeff(P_R, deg_shift, field), _poly_coeff(stage1_x, deg_shift, field));
    coeff_stage1_tilde_boundary = field.sub(coeff_stage1_tilde_boundary, _poly_coeff(cubic_x, deg_shift, field));
    coeff_stage1_tilde_boundary = field.sub(coeff_stage1_tilde_boundary, cubic_coeff);
    coeff_stage1_tilde_boundary = field.sub(coeff_stage1_tilde_boundary, stage2_at_deg_shift);

    const s2_1_shift = _scalar_shift_from_square_boundary({
      coeff_P_at_boundary: coeff_stage1_tilde_boundary,
      H: H_half,
      M: Ht_pow,
      lam: field.neg(c1),
      field,
    });
    const S2_1 = _poly_add_const(H_half, s2_1_shift, field);

    // Stage 2: recover U=(S1_2)^2 - S1_3 and the scalar shift in S2_2 = H_quarter + t.
    const K2 = _poly_mul(
      _poly_sub(H_tilde, _poly_scale_int(S2_1, k - 1, field), field),
      _poly_pow(_poly_add(H_tilde, S2_1, field), k - 3, field),
      field
    );
    const degK2 = _poly_degree(K2);
    if (degK2 !== (k - 2) * D) {
      throw new Error('internal: unexpected deg(K2) in odd-k decoder');
    }

    const stage1_tilde = _poly_mul(_poly_mul(_poly_square(S2_1, field), Ht_pow, field), [field.neg(c1)], field);
    const cubic_tilde = _poly_mul(
      _poly_mul(_poly_pow(H_tilde, k - 3, field), _poly_pow(S2_1, 3, field), field),
      [cubic_coeff],
      field
    );
    const known_stage12 = _poly_add(_poly_add(stage1_x, stage1_tilde, field), _poly_add(cubic_x, cubic_tilde, field), field);

    // High part of G2 is independent of t and equals -H_quarter^2 in degrees > D/4.
    const Hq2 = _poly_square(H_quarter, field);
    const g2_high = new Array(Math.floor(D / 2) + 1).fill(field.zero());
    for (let i = D4 + 1; i <= Math.floor(D / 2); i++) {
      g2_high[i] = field.neg(_poly_coeff(Hq2, i, field));
    }
    const g2_high_term = _poly_mul(g2_high, K2, field);

    const prod2 = new Array((k - 2) * D + Math.floor(D / 2) + 1).fill(field.zero());
    for (let d = (k - 2) * D + Math.floor(D / 2); d >= (k - 2) * D + D4; d--) {
      const pr_deg = d + 1;
      let rhs = field.sub(_poly_coeff(P_R, pr_deg, field), _poly_coeff(known_stage12, pr_deg, field));
      rhs = field.mul(rhs, inv_m);
      rhs = field.sub(rhs, _poly_coeff(g2_high_term, pr_deg, field));
      prod2[d] = field.neg(rhs);
    }

    const U_high = _recover_monic_factor_high_coeffs_from_product({
      product: prod2,
      known_factor: K1,
      factor_deg: Math.floor(D / 2),
      min_deg: D4,
      field,
    });
    const U_poly = new Array(Math.floor(D / 2) + 1).fill(field.zero());
    for (const [deg_i, coeff_i] of U_high) {
      U_poly[deg_i] = field.coerce(coeff_i);
    }
    U_poly[Math.floor(D / 2)] = field.one();
    const S1_2 = _monic_sqrt_from_high_square_coeffs(_poly_trim(U_poly, field), D4, field);

    let Q_mid = _poly_sub(S1_2, H_quarter, field);
    let q_mid_params;
    if (l === 2) {
      // In the special base construction at l==2 (Alg. `alg:constr-Tk2l-base`, odd branch),
      // S1_2 is fixed to x and carries no Q_{2^{l-2}-1} parameter block.
      Q_mid = _poly_trim(Q_mid, field);
      if (_poly_degree(Q_mid) > 0 || !field.eq(_poly_coeff(Q_mid, 0, field), field.zero())) {
        throw new Error('l==2 odd-k decoder expected S1_2 == x (no mid Q-block)');
      }
      q_mid_params = [];
    } else {
      q_mid_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: Q_mid, k: l - 2, Hs: Hs.slice(0, l - 2), field });
    }

    // Recover t := s2_2 shift at the boundary degree (k-2)D + D/4.
    const deg_t = (k - 2) * D + D4;
    let stage2_coeff = field.sub(_poly_coeff(P_R, deg_t, field), _poly_coeff(known_stage12, deg_t, field));
    stage2_coeff = field.mul(stage2_coeff, inv_m);

    // Compute the x*G1*K1 contribution at this degree using U_high's degree-(D4-1) coefficient.
    const S1_2_sq = _poly_square(S1_2, field);
    const u_d4m1 = field.sub(_poly_coeff(S1_2_sq, D4 - 1, field), field.one());
    let uk1_coeff = field.zero();
    // prod_deg = (k-2)D + (D4-1) uses only U degrees >= D4-1.
    for (let j = 0; j <= Math.floor(D / 2) - (D4 - 1); j++) {
      const udeg = (D4 - 1) + j;
      if (udeg > Math.floor(D / 2)) break;
      let ucoef;
      if (udeg === D4 - 1) {
        ucoef = u_d4m1;
      } else {
        ucoef = field.coerce(U_high.has(udeg) ? U_high.get(udeg) : field.zero());
      }
      uk1_coeff = field.add(uk1_coeff, field.mul(ucoef, _poly_coeff(K1, degK1 - j, field)));
    }
    const x_g1k1_at_deg_t = field.neg(uk1_coeff); // G1=-U, x-shift

    // Isolate g2k2 coefficient at this degree and solve t from [x^{D4}]G2 = -Hq2[D4] - 2t.
    const g2k2_coeff = field.sub(stage2_coeff, x_g1k1_at_deg_t);
    let g2_known_high = field.zero();
    for (let j = 1; j <= Math.floor(D / 2) - D4; j++) {
      const gdeg = D4 + j;
      const gcoef = field.neg(_poly_coeff(Hq2, gdeg, field));
      g2_known_high = field.add(g2_known_high, field.mul(gcoef, _poly_coeff(K2, degK2 - j, field)));
    }
    const g2_d4_coeff = field.sub(g2k2_coeff, g2_known_high);
    const s2_2_shift = field.mul(field.neg(field.add(g2_d4_coeff, _poly_coeff(Hq2, D4, field))), inv2);
    const S2_2 = _poly_add_const(H_quarter, s2_2_shift, field);

    // Recover U down to degree 1 (clean window) and then solve U0 on the contaminated boundary.
    const G2_no_const = _poly_scale_int(_poly_square(S2_2, field), -1, field);
    const g2k2_no_const = _poly_mul(G2_no_const, K2, field);

    const prod2_low = new Array((k - 2) * D + Math.floor(D / 2) + 1).fill(field.zero());
    // Clean stage-2 window: recover U down to degree 1 (inclusive), i.e. d down to (k-2)D+1.
    for (let d = (k - 2) * D + Math.floor(D / 2); d >= (k - 2) * D + 1; d--) {
      const pr_deg = d + 1;
      let rhs = field.sub(_poly_coeff(P_R, pr_deg, field), _poly_coeff(known_stage12, pr_deg, field));
      rhs = field.mul(rhs, inv_m);
      rhs = field.sub(rhs, _poly_coeff(g2k2_no_const, pr_deg, field));
      prod2_low[d] = field.neg(rhs);
    }

    const U_low = _recover_monic_factor_high_coeffs_from_product({
      product: prod2_low,
      known_factor: K1,
      factor_deg: Math.floor(D / 2),
      min_deg: 1,
      field,
    });

    const degB = (k - 2) * D + 1;
    let inner_lead;
    if (k_half % 2 === 0) {
      inner_lead = field.neg(field.mul(field.coerce(k_half), inv2));
    } else {
      inner_lead = field.neg(field.mul(field.coerce(k_half * (k_half - 1)), inv2));
    }

    let rhsB = field.sub(_poly_coeff(P_R, degB, field), _poly_coeff(stage1_x, degB, field));
    rhsB = field.sub(rhsB, _poly_coeff(stage1_tilde, degB, field));
    rhsB = field.sub(rhsB, _hatR1_combined_coeff_at_degree({ k, H, S1_1, H_tilde, S2_1, deg: degB, field }));
    rhsB = field.sub(rhsB, inner_lead);
    rhsB = field.mul(rhsB, inv_m);
    rhsB = field.sub(rhsB, _poly_coeff(g2k2_no_const, degB, field));

    // rhsB == (G1*K1)[(k-2)D] = -(U*K1)[degK1]; solve U0.
    let known_sum = field.zero();
    for (let j = 1; j <= Math.floor(D / 2); j++) {
      const uj = field.coerce(U_low.has(j) ? U_low.get(j) : field.zero());
      if (field.is_zero(uj)) continue;
      known_sum = field.add(known_sum, field.mul(uj, _poly_coeff(K1, degK1 - j, field)));
    }
    const U0 = field.sub(field.neg(rhsB), known_sum);

    // Build S1_3 = S1_2^2 - U (degree < D/4, monic degree D/4-1).
    let S1_3 = new Array(D4).fill(field.zero());
    S1_3[D4 - 1] = field.one();
    for (let i = 1; i <= D4 - 2; i++) {
      const ui = field.coerce(U_low.has(i) ? U_low.get(i) : field.zero());
      S1_3[i] = field.sub(_poly_coeff(S1_2_sq, i, field), ui);
    }
    S1_3[0] = field.sub(_poly_coeff(S1_2_sq, 0, field), U0);
    S1_3 = _poly_trim(S1_3, field);

    let q_low_params;
    if (l === 2) {
      // In the l==2 base construction, S1_3 is fixed to 0 and has no parameters.
      if (_poly_degree(S1_3) > 0 || !field.eq(_poly_coeff(S1_3, 0, field), field.zero())) {
        throw new Error('l==2 odd-k decoder expected S1_3 == 0 (no low Q-block)');
      }
      q_low_params = [];
    } else {
      q_low_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: S1_3, k: l - 2, Hs: Hs.slice(0, l - 2), field });
    }

    // Recover s2_3 from degree (k-2)D (clean of inner recursion and head).
    const degC = (k - 2) * D;
    let rhsC = field.sub(_poly_coeff(P_R, degC, field), _poly_coeff(stage1_x, degC, field));
    rhsC = field.sub(rhsC, _poly_coeff(stage1_tilde, degC, field));
    rhsC = field.sub(rhsC, _hatR1_combined_coeff_at_degree({ k, H, S1_1, H_tilde, S2_1, deg: degC, field }));
    rhsC = field.mul(rhsC, inv_m);

    // Subtract x*G1*K1 and the known -S2_2^2*K2 part to isolate the constant s2_3.
    const U_full = new Array(Math.floor(D / 2) + 1).fill(field.zero());
    for (const [deg_i, coeff_i] of U_low) {
      U_full[deg_i] = field.coerce(coeff_i);
    }
    U_full[0] = U0;
    U_full[Math.floor(D / 2)] = field.one();
    const x_g1k1_at_degC = _poly_coeff(_poly_shift_xk(_poly_mul(_poly_scale_int(U_full, -1, field), K1, field), 1, field), degC, field);
    rhsC = field.sub(rhsC, x_g1k1_at_degC);
    rhsC = field.sub(rhsC, _poly_coeff(g2k2_no_const, degC, field));

    // rhsC is affine in the unknown scalar s2_3 (tail[0]), but can include a fixed
    // contribution from the inner recursion / head gadget that is independent of s2_3.
    //
    // Compute and subtract that fixed part by evaluating the same expression on a
    // synthetic instance where head/mid are zero and s2_3 is set to 0, while all
    // other already-recovered tail parameters are kept.
    const alpha_synth = new Array(total).fill(field.zero());
    const tail_synth = new Array(D).fill(field.zero());
    // tail layout: [s2_3] + q_low + [s2_2_shift] + q_mid + [s2_1_shift] + q_hi
    tail_synth[0] = field.zero();
    for (const [i, v] of q_low_params.entries()) {
      tail_synth[1 + i] = v;
    }
    tail_synth[Math.floor(D / 4)] = s2_2_shift;
    for (const [i, v] of q_mid_params.entries()) {
      tail_synth[Math.floor(D / 4) + 1 + i] = v;
    }
    tail_synth[Math.floor(D / 2)] = s2_1_shift;
    for (const [i, v] of q_hi_params.entries()) {
      tail_synth[Math.floor(D / 2) + 1 + i] = v;
    }
    const tail_start = D + ((k - 3) * D);
    for (const [i, v] of tail_synth.entries()) {
      alpha_synth[tail_start + i] = v;
    }
    const P_R_synth = _poly_remainder_poly_from_T({ k, l, alpha: alpha_synth, Hs, tilde_H_2l: H_tilde, field });

    let rhsC_synth = field.sub(_poly_coeff(P_R_synth, degC, field), _poly_coeff(stage1_x, degC, field));
    rhsC_synth = field.sub(rhsC_synth, _poly_coeff(stage1_tilde, degC, field));
    rhsC_synth = field.sub(
      rhsC_synth,
      _hatR1_combined_coeff_at_degree({ k, H, S1_1, H_tilde, S2_1, deg: degC, field })
    );
    rhsC_synth = field.mul(rhsC_synth, inv_m);
    rhsC_synth = field.sub(rhsC_synth, x_g1k1_at_degC);
    rhsC_synth = field.sub(rhsC_synth, _poly_coeff(g2k2_no_const, degC, field));

    const s2_3 = field.sub(rhsC, rhsC_synth);

    // Assemble tail alpha layout (exactly as `_poly_paper_T`, odd case l>=3).
    tail_out = new Array(D).fill(field.zero());
    tail_out[0] = s2_3;
    for (const [i, v] of q_low_params.entries()) {
      tail_out[1 + i] = v;
    }
    tail_out[Math.floor(D / 4)] = s2_2_shift;
    for (const [i, v] of q_mid_params.entries()) {
      tail_out[Math.floor(D / 4) + 1 + i] = v;
    }
    tail_out[Math.floor(D / 2)] = s2_1_shift;
    for (const [i, v] of q_hi_params.entries()) {
      tail_out[Math.floor(D / 2) + 1 + i] = v;
    }
  }

  // ---- Head + mid parameters via descending pivots of the frozen-tail map. ----
  const rest_len = total - D;

  function _rest_remainder(rest) {
    const al = rest.concat(tail_out);
    return _poly_remainder_poly_from_T({ k, l, alpha: al, Hs, tilde_H_2l: H_tilde, field });
  }

  const rest = _decode_by_descending_pivots({
    target: P_R, encode_fn: _rest_remainder, nparams: rest_len, field, what: `R_odd(k=${k},l=${l})`,
  });

  const alphas_out = rest.concat(tail_out);
  if (alphas_out.length !== total) {
    throw new Error('internal: odd-k alpha length mismatch');
  }
  const [_T1, _T2, Hs_out, tilde_out] = _poly_paper_T({
    k, l, alpha: alphas_out, Hs, tilde_H_2l: H_tilde, field,
  });
  return [alphas_out, Hs_out, tilde_out];
}

// ====================================================================
// BEGIN g1_emit_bases.frag.js
// ====================================================================
// g1_emit_bases.frag.js — chain emitters I (ChainBuilder side) for the char-0
// lane port of tools/poly_schedule.py.
// Fragment: function declarations only. No imports, no exports, no top-level
// side effects. Runtime (Field, AffineForm, ChainBuilder, _affine_scale_int,
// PEELED_Q, ...) and cross-group emitters (_paper_Q_2lp1k_minus_1_with_powers)
// are supplied by other fragments at assembly time.

// py: tools/poly_schedule.py:424
// One-multiplication helper: (A+B)(A-B).
function _paper_square_diff(builder, A, B, name = null) {
  const field = builder.field;
  return builder.mul(A.add(B, field), A.sub(B, field), name);
}

// py: tools/poly_schedule.py:431
// Base known power:
//     H_2[α0,α1](x) = (x + α1)x + α0
function _paper_H2(builder, alpha0, alpha1) {
  const field = builder.field;
  const x = builder.x;
  const t = builder.withLabel('H_2 base', () =>
    builder.mul(x.add_const(field.coerce(alpha1), field), x));
  return t.add_const(field.coerce(alpha0), field);
}

// py: tools/poly_schedule.py:443
// Q_3[α0,α1,α2](x, H2) = (x + α2)(H2 + α1) + α0
//
// This uses 1 multiplication, assuming H2 is already available.
function _paper_q3(builder, alpha0, alpha1, alpha2, H2) {
  const field = builder.field;
  const x = builder.x;
  const a0 = field.coerce(alpha0);
  const a1 = field.coerce(alpha1);
  const a2 = field.coerce(alpha2);
  const t = builder.withLabel('Q_3 known-power block', () =>
    builder.mul(x.add_const(a2, field), H2.add_const(a1, field)));
  return t.add_const(a0, field);
}

// py: tools/poly_schedule.py:459
// Paper base construction for degree 5 (3 multiplications):
//
//   P5[α0..α4](x) = (x + α2) * ( (x^2 + α4) * (x^2 + x + α3) + α1 ) + α0
//
// This is the degree-5 base used by the paper family `P_n[α]` and matches the
// `n==5` chain in `_compile_paper_monic` (when the polynomial coefficients are
// interpreted as α-parameters).
function _paper_P5(builder, alpha) {
  const field = builder.field;
  if (alpha.length !== 5) {
    throw new Error(`P5 needs 5 params, got ${alpha.length}`);
  }
  const a0 = field.coerce(alpha[0]);
  const a1 = field.coerce(alpha[1]);
  const a2 = field.coerce(alpha[2]);
  const a3 = field.coerce(alpha[3]);
  const a4 = field.coerce(alpha[4]);

  const x = builder.x;
  builder.pushLabel('P_5 base');
  const x2 = builder.mul(x, x);
  const z = builder.mul(x2.add_const(a4, field), x2.add(x, field).add_const(a3, field));
  const w = builder.mul(x.add_const(a2, field), z.add_const(a1, field));
  builder.popLabel();
  return w.add_const(a0, field);
}

// py: tools/poly_schedule.py:482
// Septic base construction (degree 7, 4 multiplications).
//
// This matches the "paper-style" chain used by `_compile_paper_monic` for n=7
// (where it is shown to be decodable in characteristic != 2).
//
//     y = x * (x + α6)
//     z = (α5 + x + y) * (α4 + x)
//     w = (α3 + z) * x
//     v = (α2 + x + z) * (α1 + w)
//     P7 = α0 + y + w + v
function _paper_P7(builder, alpha) {
  if (alpha.length !== 7) {
    throw new Error(`P7 needs 7 params, got ${alpha.length}`);
  }

  const field = builder.field;
  alpha = alpha.map((a) => field.coerce(a));
  const x = builder.x;

  builder.pushLabel('P_7 base');
  const y = builder.mul(x, x.add_const(alpha[6], field));
  const z = builder.mul(x.add(y, field).add_const(alpha[5], field), x.add_const(alpha[4], field));
  const w = builder.mul(z.add_const(alpha[3], field), x);
  const v = builder.mul(x.add(z, field).add_const(alpha[2], field), w.add_const(alpha[1], field));
  builder.popLabel();
  return y.add(w, field).add(v, field).add_const(alpha[0], field);
}

// py: tools/poly_schedule.py:580
// Construct the pair (T^{(1)}_{k,2^l}, T^{(2)}_{k,2^l}) from sections/constructions.tex.
//
// This is the core subroutine used for the 4k+1 family; it also produces (as a
// byproduct) higher known powers H_{2^{l+1}} / \tilde H_{2^{l+1}} in the
// recursive cases.
//
// Args:
//     k: positive integer
//     l: >= 1 (so 2^l >= 2)
//     alpha: parameter list of length (k-1)*2^l
//     Hs: known powers list with Hs[i] = H_{2^i}, Hs[0]=x, len(Hs) >= l+1
//     tilde_H_2l: the \tilde H_{2^l} input for the second component
//
// Returns:
//     [T1, T2, Hs_out, tilde_H_out] where:
//       - T1, T2 are the constructed polynomials
//       - Hs_out extends Hs with any newly constructed H_{2^i}
//       - tilde_H_out is the corresponding \tilde H_{2^{l'}} at the output scale
function _paper_T(builder, k, l, alpha, Hs, tilde_H_2l) {
  // JS-only provenance wrapper: every gate of this T level (and, via nested
  // pushes, its sub-gadgets) is attributed to T_{k,2^l}.
  return builder.withLabel(`T-recursion T_{${k},${1 << l}} (l=${l})`, () =>
    _paper_T_impl(builder, k, l, alpha, Hs, tilde_H_2l));
}

function _paper_T_impl(builder, k, l, alpha, Hs, tilde_H_2l) {
  const field = builder.field;
  const two = field.add(field.one(), field.one());
  const is_char2 = field.is_zero(two);
  if (k < 1) {
    throw new Error('T requires k >= 1');
  }
  if (l < 1) {
    throw new Error('T requires l >= 1');
  }
  if (Hs.length <= l) {
    throw new Error(`T(k=${k},l=${l}) requires Hs up to index ${l} (H_{2^${l}})`);
  }

  const block = 1 << l;
  const need = (k - 1) * block;
  if (alpha.length !== need) {
    throw new Error(`T(k=${k},l=${l}) needs ${k - 1}*2^${l}=${need} alpha params, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  if (k === 1) {
    // Base: T^{(1)} = H_{2^l}, T^{(2)} = \tilde H_{2^l}.
    return [Hs[l], tilde_H_2l, Hs, tilde_H_2l];
  }

  // Even k
  if (k % 2 === 0) {
    // Split: prefix params for recursion, tail block for constructing new powers.
    const rec_len = (Math.floor(k / 2) - 1) * (2 * block);
    const tail = alpha.slice(rec_len);
    const rec_params = alpha.slice(0, rec_len);
    if (tail.length !== block) {
      throw new Error('internal error: T even tail length mismatch');
    }

    // Special case: l = 1 (paper Algorithm `alg:constr-Tk2l-base`, even-k branch).
    if (l === 1) {
      // H4 = (H2 + (x + a1))(H2 - (x + a1)) + a0
      // tilde_H4 = H4 + (tilde_H2-H2)
      const a0 = tail[0];
      const a1 = tail[1];
      const x = builder.x;
      // In all paper call-sites, tilde_H2 is a scalar shift of H2.
      const delta = tilde_H_2l.sub(Hs[1], field);
      const can_fast_shift = delta.terms.size === 0;
      let delta_int = null;
      if (can_fast_shift) {
        try {
          // works for GF(p) elements represented as ints
          // (Python's int(delta.const); over Q, int(Fraction) truncates toward zero.)
          if (typeof delta.const === 'bigint') {
            delta_int = Number(delta.const);
          } else {
            delta_int = Number(delta.const.n / delta.const.d);
          }
          if (!Number.isSafeInteger(delta_int)) throw new Error('not an int');
        } catch (e) {
          delta_int = null;
        }
      }
      let H4;
      let tilde_H4;
      if (is_char2) {
        // Characteristic-2 replacement: H4 = H2 * (H2 + (x + a1)) + a0.
        //
        // This avoids the `(A+B)(A-B)` square-difference gadget, which collapses
        // in char 2, and is decodable given H2 by polynomial division.
        H4 = builder.mul(Hs[1], Hs[1].add(x.add_const(a1, field), field)).add_const(a0, field);
        if (delta_int !== null) {
          // In char 2: (H2+δ)(H2+δ+x+a1) = H2(H2+x+a1) + δ(x+a1) + δ^2.
          const delta_sq = field.mul(delta.const, delta.const);
          const delta_x_plus = _affine_scale_int(field, x.add_const(a1, field), delta_int);
          tilde_H4 = H4.add(delta_x_plus, field).add_const(delta_sq, field);
        } else {
          tilde_H4 = builder
            .mul(tilde_H_2l, tilde_H_2l.add(x.add_const(a1, field), field))
            .add_const(a0, field);
        }
      } else {
        const t_plus = Hs[1].add(x.add_const(a1, field), field);
        const t_minus = Hs[1].sub(x.add_const(a1, field), field);
        H4 = builder.withLabel('H_4 known power', () => builder.mul(t_plus, t_minus))
          .add_const(a0, field);
        if (!can_fast_shift) {
          throw new Error('The shared l=1 base requires tilde_H2-H2 to be scalar');
        }
        // This is the exact-count repair: the shifted quartic is a
        // scalar shift of the first quartic, so no second product is
        // needed.
        tilde_H4 = H4.add(delta, field);
      }
      const Hs_next = Hs.slice();
      if (Hs_next.length <= 2) {
        while (Hs_next.length < 3) Hs_next.push(AffineForm.const_only(field.zero()));
      }
      Hs_next[2] = H4;
      return _paper_T(builder, Math.floor(k / 2), l + 1, rec_params, Hs_next, tilde_H4);
    }

    // Main even case: l >= 2.
    const half = 1 << (l - 1);
    const q_hi = _paper_Q_known_powers(builder, l - 1, tail.slice(half + 1), Hs.slice(0, l - 1));
    const q_lo = _paper_Q_known_powers(builder, l - 1, tail.slice(1, half), Hs.slice(0, l - 1));

    const S1_1 = Hs[l - 1].add(q_hi, field);
    const S1_2 = q_lo;
    let H_next;
    if (is_char2) {
      // Char-2 replacement: H_next = H * (H + S1_1) + S1_2.
      H_next = builder.mul(Hs[l], Hs[l].add(S1_1, field)).add(S1_2, field);
    } else {
      H_next = builder.withLabel(`H_${1 << (l + 1)} known power`, () =>
        builder.mul(Hs[l].add(S1_1, field), Hs[l].sub(S1_1, field))).add(S1_2, field);
    }

    const S2_1 = Hs[l - 1].add_const(tail[half], field);
    const S2_2 = tail[0];
    let tilde_next;
    if (is_char2) {
      tilde_next = builder.mul(tilde_H_2l, tilde_H_2l.add(S2_1, field)).add_const(S2_2, field);
    } else {
      tilde_next = builder.withLabel(`H̃_${1 << (l + 1)} shifted power`, () => builder
        .mul(tilde_H_2l.add(S2_1, field), tilde_H_2l.sub(S2_1, field)))
        .add_const(S2_2, field);
    }

    const Hs_next = Hs.slice();
    if (Hs_next.length <= l + 1) {
      while (Hs_next.length < l + 2) Hs_next.push(AffineForm.const_only(field.zero()));
    }
    Hs_next[l + 1] = H_next;
    return _paper_T(builder, Math.floor(k / 2), l + 1, rec_params, Hs_next, tilde_next);
  }

  // Odd k
  const m = Math.floor((k - 1) / 2);
  if (l === 2) {
    // Special case: k odd, l = 2 (paper Algorithm `alg:constr-Tk2l-base`, odd-k branch).
    //
    // Layout: head block (size 4) + mid (for recursion) + tail block (size 4).
    if (block !== 4) {
      throw new Error('internal error: expected block=4 for l=2');
    }

    const head = alpha.slice(0, 4);
    const tail = alpha.slice(-4);
    const mid = alpha.slice(4, -4);

    // Tail parameters:
    //   tail[0]=α_{4k-8} : shift from H8 to tilde_H8
    //   tail[1]=α_{4k-7} : S1_3
    //   tail[2]=α_{4k-6} : S1_2 shift in (x+α)
    //   tail[3]=α_{4k-5} : shift in S1_1 = H2 + (x+α)
    const next_shift = tail[0];
    const s1_3 = tail[1];
    const s1_2_shift = tail[2];
    const s1_1_shift = tail[3];

    // First-branch (unshifted) auxiliaries:
    //   S1_1 = H2 + (x + s1_1_shift)
    //   S1_2 = x + s1_2_shift
    //   S1_3 = s1_3
    const S1_1 = Hs[1].add(builder.x.add_const(s1_1_shift, field), field);
    const core = Hs[2].add(S1_1, field);
    const S1_2 = builder.x.add_const(s1_2_shift, field);
    const H8 = builder.withLabel('H_8 known power', () =>
      builder.mul(core.add(S1_2, field), core.sub(S1_2, field))).add_const(s1_3, field);

    const Hs_next = Hs.slice();
    if (Hs_next.length <= 3) {
      while (Hs_next.length < 4) Hs_next.push(AffineForm.const_only(field.zero()));
    }
    Hs_next[3] = H8;

    // The input quartics differ by a scalar rho.  Put S2_1=S1_1-rho,
    // S2_2=S1_2 and S2_3=S1_3+next_shift.  The square-difference cores
    // are then identical, so tilde_H8=H8+next_shift shares the H8 gate.
    const rho = tilde_H_2l.sub(Hs[2], field);
    if (rho.terms.size) {
      throw new Error('The shared odd l=2 base requires tilde_H4-H4 to be scalar');
    }
    const S2_1 = S1_1.sub(rho, field);
    const tilde_H8 = H8.add_const(next_shift, field);

    const [T1_rec, T2_rec, Hs_out, tilde_out] = _paper_T(builder, m, l + 1, mid, Hs_next, tilde_H8);

    // Q3(head[1..3]) is the additive term on the first branch.
    const q3 = _paper_Q_known_powers(builder, 2, head.slice(1), Hs.slice(0, 2));

    // (H4 - (k-1)S1_1) * T1_rec + Q3
    const factor1 = Hs[2].sub(_affine_scale_int(field, S1_1, k - 1), field);
    const T1 = builder.mul(factor1, T1_rec).add(q3, field);

    // (tilde_H4 - (k-1)S2_1) * T2_rec + α0
    const factor2 = tilde_H_2l.sub(_affine_scale_int(field, S2_1, k - 1), field);
    const T2 = builder.mul(factor2, T2_rec).add_const(head[0], field);
    return [T1, T2, Hs_out, tilde_out];
  }

  if (l < 3) {
    throw new Error('T odd case requires l >= 3 (or special l=2)');
  }

  // Main odd case: l >= 3.
  // Layout: head block (size 2^l) + mid (for recursion) + tail block (size 2^l).
  const head = alpha.slice(0, block);
  const tail = alpha.slice(-block);
  const mid = alpha.slice(block, -block);

  const half = 1 << (l - 1);
  const quarter = 1 << (l - 2);

  // H_{2^{l+1}} = ((H_{2^l} + S1_1) + S1_2) * ((H_{2^l} + S1_1) - S1_2) + S1_3
  const q_hi = _paper_Q_known_powers(builder, l - 1, tail.slice(half + 1), Hs.slice(0, l - 1));
  const S1_1 = Hs[l - 1].add(q_hi, field);

  const q_mid = _paper_Q_known_powers(builder, l - 2, tail.slice(quarter + 1, half), Hs.slice(0, l - 2));
  const S1_2 = Hs[l - 2].add(q_mid, field);

  const S1_3 = _paper_Q_known_powers(builder, l - 2, tail.slice(1, quarter), Hs.slice(0, l - 2));

  const base = Hs[l].add(S1_1, field);
  const H_next = builder.withLabel(`H_${1 << (l + 1)} known power`, () =>
    builder.mul(base.add(S1_2, field), base.sub(S1_2, field))).add(S1_3, field);

  const S2_1 = Hs[l - 1].add_const(tail[half], field);
  const S2_2 = Hs[l - 2].add_const(tail[quarter], field);
  const S2_3 = tail[0];
  const base2 = tilde_H_2l.add(S2_1, field);
  const tilde_next = builder.withLabel(`H̃_${1 << (l + 1)} shifted power`, () =>
    builder.mul(base2.add(S2_2, field), base2.sub(S2_2, field))).add_const(S2_3, field);

  const Hs_next = Hs.slice();
  if (Hs_next.length <= l + 1) {
    while (Hs_next.length < l + 2) Hs_next.push(AffineForm.const_only(field.zero()));
  }
  Hs_next[l + 1] = H_next;

  const [T1_rec, T2_rec, Hs_out, tilde_out] = _paper_T(builder, m, l + 1, mid, Hs_next, tilde_next);

  const q_low = _paper_Q_known_powers(builder, l, head.slice(1), Hs.slice(0, l));
  const factor1 = Hs[l].sub(_affine_scale_int(field, S1_1, k - 1), field);
  const T1 = builder.mul(factor1, T1_rec).add(q_low, field);

  const factor2 = tilde_H_2l.sub(_affine_scale_int(field, S2_1, k - 1), field);
  const T2 = builder.mul(factor2, T2_rec).add_const(head[0], field);
  return [T1, T2, Hs_out, tilde_out];
}

// py: tools/poly_schedule.py:1782
// 2-adic valuation v2(n) for n>0: largest e such that 2^e | n.
function _v2_positive(n) {
  if (n <= 0) {
    throw new Error('v2_positive requires n > 0');
  }
  let e = 0;
  while ((n & 1) === 0) {
    n >>= 1;
    e += 1;
  }
  return e;
}

// py: tools/poly_schedule.py:1794
// Peeled monic family for any odd degree, given the tower up to
// `H_{2^{floor(log2 deg)}}`:
//
//     QO(d) = (H_h + U) * W + B,   h = 2^{floor(log2 d)},
//     U = QO(2h-d) inside the factor, W = B = QO(d-h),
//
// with Mersenne degrees delegating to the (peeled) known-powers gadget.
// Exactly (d-1)/2 multiplications; parameter layout [U..., W..., B...].
function _paper_QO(builder, deg, alpha, Hs) {
  const field = builder.field;
  if (deg < 1 || deg % 2 === 0) {
    throw new Error('QO requires odd deg >= 1');
  }
  if (alpha.length !== deg) {
    throw new Error(`QO(deg=${deg}) needs ${deg} params, got ${alpha.length}`);
  }
  if (deg === 1) {
    return builder.x.add_const(field.coerce(alpha[0]), field);
  }
  const t = 32 - Math.clz32(deg); // deg.bit_length() for positive Number
  if (deg === (1 << t) - 1) {
    return _paper_Q_known_powers(builder, t, alpha, Hs.slice(0, t));
  }
  const h = 1 << (t - 1);
  const w = deg - h;
  const ud = 2 * h - deg;
  const U = _paper_QO(builder, ud, alpha.slice(0, ud), Hs);
  const W = _paper_QO(builder, w, alpha.slice(ud, ud + w), Hs);
  const B = _paper_QO(builder, w, alpha.slice(ud + w), Hs);
  return builder.mark_value(
    builder.withLabel(`Q_${deg} peeled block`, () => builder.mul(Hs[t - 1].add(U, field), W))
      .add(B, field));
}

// py: tools/poly_schedule.py:1843
// Dispatch helper: for any odd `deg >= 1`, write
//     deg = 2^l * (2k+1) - 1
// where `l = v2(deg+1) >= 1`, and call the known-powers construction
//     Q_{2^{l+1}k + (2^l - 1)} = Q_deg.
//
// Returns:
//     [Q_deg, Hs_out, tilde_out]
function _paper_Q_for_odd_degree_with_powers(builder, deg, alpha, Hs) {
  if (deg < 1 || deg % 2 === 0) {
    throw new Error('Q_for_odd_degree requires odd deg >= 1');
  }
  const l = _v2_positive(deg + 1);
  const odd = (deg + 1) >> l; // == 2k+1
  if (odd % 2 === 0) {
    throw new Error('internal error: expected odd factor (deg+1)/2^l to be odd');
  }
  const k = Math.floor((odd - 1) / 2);
  if (PEELED_Q && deg >= 3 && Hs.length >= 32 - Math.clz32(deg)) {
    return [_paper_QO(builder, deg, alpha, Hs), Hs.slice(), Hs[0]];
  }
  return _paper_Q_2lp1k_minus_1_with_powers(builder, k, l, alpha, Hs);
}

// py: tools/poly_schedule.py:1871
// Fill construction A_{2^l} from sections/constructions.tex (Algorithm `alg:constr-fill`).
//
// Inputs:
//   - l >= 1
//   - alpha: [α0..α_{2^{l+1}-3}] (length 2^{l+1}-2)
//   - beta:  [β0..β_{2^l}]      (length 2^l+1)
//   - S1_2l, S2_2l: the compatible pair components at scale 2^l
//   - Hs: list of known powers, with Hs[i] = H_{2^i} and Hs[0] = x
//         (so len(Hs) >= l+1)
//
// Output:
//   - A_{2^l} = (x + β0) A^{(1)}_{2^l} + A^{(2)}_{2^l}
function _paper_A_fill(builder, l, alpha, beta, S1_2l, S2_2l, Hs) {
  const field = builder.field;
  if (l < 0) {
    throw new Error('A_fill requires l >= 0');
  }
  if (l > 0 && Hs.length <= l) {
    throw new Error(`A_fill requires Hs up to index ${l} (H_{2^${l}})`);
  }

  const need_alpha = (1 << (l + 1)) - 2;
  const need_beta = (1 << l) + 1;
  if (alpha.length !== need_alpha) {
    throw new Error(`A_fill l=${l} needs ${need_alpha} alpha params, got ${alpha.length}`);
  }
  if (beta.length !== need_beta) {
    throw new Error(`A_fill l=${l} needs ${need_beta} beta params, got ${beta.length}`);
  }

  // Coerce parameters once.
  alpha = alpha.map((a) => field.coerce(a));
  beta = beta.map((b) => field.coerce(b));

  function A1(l_, S1) {
    if (l_ === 0) {
      return S1;
    }
    if (l_ === 1) {
      // A^{(1)}_2 = (H2 + β1) S1 + α1
      const t = builder.mul(Hs[1].add_const(beta[1], field), S1);
      return t.add_const(alpha[1], field);
    }

    if (l_ === 2) {
      // S^{(1)}_2 = (H4 + β3) S^{(1)}_4 + Q_3[α3,α4,α5](x,H2)
      const q3 = _paper_q3(builder, alpha[3], alpha[4], alpha[5], Hs[1]);
      const t = builder.mul(Hs[2].add_const(beta[3], field), S1);
      const S1_2 = t.add(q3, field);
      // A^{(1)}_4 = A^{(1)}_2[α0,α1,β2,β1](S^{(1)}_2,(x,H2))
      const t2 = builder.mul(Hs[1].add_const(beta[1], field), S1_2);
      return t2.add_const(alpha[1], field);
    }

    // l_ >= 3:
    // S^{(1)}_{2^{l_-1}} = (H_{2^{l_}} + Q_{2^{l_-1}-1}[β_{2^{l_}-1}..β_{2^{l_-1}+1}]) S^{(1)}_{2^{l_}}
    //                  + Q_{2^{l_}-1}[α_{2^{l_}-1}..α_{2^{l_+1}-3}]
    const k_small = l_ - 1; // Q_{2^{k_small}-1}
    if (k_small < 2) {
      throw new Error('internal error: expected k_small >= 2 for l_>=3');
    }

    // sections/constructions.tex writes this Q polynomial as
    //   Q_{2^{l_-1}-1}[β_{2^{l_}-1}, ..., β_{2^{l_-1}+1}],
    // i.e. parameters in *descending* β-index order.
    const q_small_params = beta.slice((1 << (l_ - 1)) + 1, 1 << l_).reverse();
    const q_small = _paper_Q_known_powers(builder, k_small, q_small_params, Hs.slice(0, l_ - 1));

    const factor = Hs[l_].add(q_small, field);
    const t = builder.mul(factor, S1);

    const q_big_params = alpha.slice((1 << l_) - 1, (1 << (l_ + 1)) - 2);
    const q_big = _paper_Q_known_powers(builder, l_, q_big_params, Hs.slice(0, l_));
    const S1_prev = t.add(q_big, field);
    return A1(l_ - 1, S1_prev);
  }

  function A2(l_, S2) {
    if (l_ === 0) {
      return S2;
    }
    if (l_ === 1) {
      // A^{(2)}_2 = (H2 + β2) S2 + α0
      const t = builder.mul(Hs[1].add_const(beta[2], field), S2);
      return t.add_const(alpha[0], field);
    }

    if (l_ === 2) {
      // S^{(2)}_2 = (H4 + β4) S^{(2)}_4 + α2
      const t = builder.mul(Hs[2].add_const(beta[4], field), S2);
      const S2_2 = t.add_const(alpha[2], field);
      // A^{(2)}_4 = A^{(2)}_2[α0,α1,β2,β1](S^{(2)}_2,(x,H2))
      const t2 = builder.mul(Hs[1].add_const(beta[2], field), S2_2);
      return t2.add_const(alpha[0], field);
    }

    // l_ >= 3:
    // S^{(2)}_{2^{l_-1}} = (H_{2^{l_}} + β_{2^{l_}}) S^{(2)}_{2^{l_}} + α_{2^{l_}-2}
    const t = builder.mul(Hs[l_].add_const(beta[1 << l_], field), S2);
    const S2_prev = t.add_const(alpha[(1 << l_) - 2], field);
    return A2(l_ - 1, S2_prev);
  }

  const A1_out = A1(l, S1_2l);
  const A2_out = A2(l, S2_2l);

  if (l === 0) {
    // Base (not explicitly spelled out in sections/constructions.tex, but needed for the l=1
    // instance of the "4k+1 using known powers" construction):
    //
    //   A_1 = (x + β0) * S1 + S2 + β1
    //
    // This matches the "(x+α)-extraction" pattern while keeping β1 as an
    // independent additive parameter.
    const t = builder.mul(builder.x.add_const(beta[0], field), A1_out);
    return t.add(A2_out, field).add_const(beta[1], field);
  }

  const out = builder.mul(builder.x.add_const(beta[0], field), A1_out).add(A2_out, field);
  return out;
}

// py: tools/poly_schedule.py:1990
function _paper_Q_known_powers(builder, k, alpha, Hs) {
  // JS-only provenance: k<=2 emits no gates of its own (k=2 delegates to the
  // Q_3 gadget, which labels itself), so only k>=3 opens a block scope.
  const run = () => _paper_Q_known_powers_impl(builder, k, alpha, Hs);
  if (k < 3) return builder.mark_value(run());
  const label = `Q_${(1 << k) - 1} known-power block${PEELED_Q ? ' (peeled)' : ''}`;
  return builder.mark_value(builder.withLabel(label, run));
}

// py: tools/poly_schedule.py:1999
// Known-powers construction Q_{2^k-1} from sections/constructions.tex (Algorithm `alg:constr-known-2n-1`).
//
// Inputs:
//   - k >= 2
//   - alpha: [α0..α_{2^k-2}] (length 2^k-1)
//   - Hs: list of known powers with Hs[i]=H_{2^i}, Hs[0]=x, and len(Hs) >= k
//
// Output:
//   - Q_{2^k-1}(x, H2, ..., H_{2^{k-1}})
function _paper_Q_known_powers_impl(builder, k, alpha, Hs) {
  const field = builder.field;
  if (k < 0) {
    throw new Error('Q_known_powers requires k >= 0');
  }
  const need = k === 0 ? 1 : (1 << k) - 1;
  if (alpha.length !== need) {
    throw new Error(`Q_known_powers k=${k} needs ${need} alpha params, got ${alpha.length}`);
  }
  if (k >= 1 && Hs.length <= k - 1) {
    throw new Error(`Q_known_powers k=${k} needs Hs up to index ${k - 1} (H_{2^${k - 1}})`);
  }

  alpha = alpha.map((a) => field.coerce(a));

  if (PEELED_Q && k >= 3) {
    const m = (1 << (k - 1)) - 1;
    const gamma = alpha[0];
    const W = _paper_Q_known_powers(builder, k - 1, alpha.slice(1, 1 + m), Hs.slice(0, k - 1));
    const B = _paper_Q_known_powers(builder, k - 1, alpha.slice(1 + m), Hs.slice(0, k - 1));
    return builder.mul(Hs[k - 1].add_const(gamma, field), W).add(B, field);
  }

  if (k === 0) {
    // Q_0[α0] is just a constant.
    return AffineForm.const_only(alpha[0]);
  }

  if (k === 1) {
    // Q_1[α0](x) = x + α0
    return builder.x.add_const(alpha[0], field);
  }

  if (k === 2) {
    // Q_3[α0,α1,α2](x,H2)
    return _paper_q3(builder, alpha[0], alpha[1], alpha[2], Hs[1]);
  }

  if (k === 3) {
    // S^{(1)}_2 = H4 + α3
    // S^{(2)}_2 = H4 + α2
    // Q_7[α0..α6](x,H2,H4) = A_2[α0,α1,β2=α4,β1=α5,β0=α6](S1,S2,(x,H2))
    const S1 = Hs[2].add_const(alpha[3], field);
    const S2 = Hs[2].add_const(alpha[2], field);
    const a_alpha = [alpha[0], alpha[1]]; // α0..α1
    const beta_block = [alpha[4], alpha[5], alpha[6]]; // corresponds to β2,β1,β0 in that order
    const beta = [field.zero(), field.zero(), field.zero()]; // β0..β2
    // Map alpha[4+i] -> β_{2-i}.
    for (let i = 0; i < beta_block.length; i++) {
      beta[2 - i] = beta_block[i];
    }
    return _paper_A_fill(builder, 1, a_alpha, beta, S1, S2, Hs.slice(0, 2));
  }

  // k >= 4:
  // S^{(1)}_{2^{k-2}} = H_{2^{k-1}} + Q_{2^{k-2}-1}[α_{2^{k-1}-1}..α_{2^{k-1}+2^{k-2}-3}]
  // S^{(2)}_{2^{k-2}} = H_{2^{k-1}} + α_{2^{k-1}-2}
  // Q_{2^k-1} = A_{2^{k-2}}[α0..α_{2^{k-1}-3}, β_{2^{k-2}}..β0](S1,S2,(x,H2..H_{2^{k-2}}))
  const sub_k = k - 2;
  const sub_start = (1 << (k - 1)) - 1;
  const sub_end = (1 << (k - 1)) + (1 << (k - 2)) - 2;
  const q_sub_params = alpha.slice(sub_start, sub_end);
  const q_sub = _paper_Q_known_powers(builder, sub_k, q_sub_params, Hs.slice(0, k - 2));

  const S1 = Hs[k - 1].add(q_sub, field);
  const S2 = Hs[k - 1].add_const(alpha[(1 << (k - 1)) - 2], field);

  const a_alpha = alpha.slice(0, (1 << (k - 1)) - 2); // α0..α_{2^{k-1}-3}

  const beta_block_start = (1 << (k - 1)) + (1 << (k - 2)) - 2;
  const beta_block = alpha.slice(beta_block_start);
  const l = k - 2;
  const need_beta = (1 << l) + 1;
  if (beta_block.length !== need_beta) {
    throw new Error(
      `internal error: expected ${need_beta} beta-block params for k=${k}, got ${beta_block.length}`
    );
  }
  const beta = [];
  for (let i = 0; i < need_beta; i++) beta.push(field.zero()); // β0..β_{2^l}
  for (let i = 0; i < beta_block.length; i++) {
    beta[(1 << l) - i] = beta_block[i];
  }

  return _paper_A_fill(builder, l, a_alpha, beta, S1, S2, Hs.slice(0, l + 1));
}

// ====================================================================
// BEGIN g2_emit_barQ.frag.js
// ====================================================================
// g2_emit_barQ.frag.js — chain emitters II for the char-0 lane port of
// tools/poly_schedule.py: Q_{2^{l+1}k-1} with powers, the barQ family,
// _paper_splittable_pair, and the public entry compile_paper_params_chain.
// Fragment: function declarations only; assembled into core.js.

// py: tools/poly_schedule.py:840
// Like `_paper_Q_2lp1k_minus_1`, but also returns the (possibly extended) list
// of known powers produced along the way, plus the terminal `\tilde H` from the
// internal `T` call.
//
// Returns: [Q, Hs_out, tilde_out]
function _paper_Q_2lp1k_minus_1_with_powers(builder, k, l, alpha, Hs) {
  // JS-only provenance wrapper: Q_{2^{l+1}k + 2^l - 1} block (k=0 delegates to
  // the plain known-powers gadget, which labels itself).
  if (k === 0) return _paper_Q_2lp1k_minus_1_with_powers_impl(builder, k, l, alpha, Hs);
  const deg = (1 << (l + 1)) * k + ((1 << l) - 1);
  return builder.withLabel(`Q_${deg} block (2^{l+1}k+2^l−1, k=${k}, l=${l})`, () =>
    _paper_Q_2lp1k_minus_1_with_powers_impl(builder, k, l, alpha, Hs));
}

function _paper_Q_2lp1k_minus_1_with_powers_impl(builder, k, l, alpha, Hs) {
  const field = builder.field;
  if (k < 0 || l < 1) {
    throw new Error('Q_2lp1k_minus_1 requires k>=0 and l>=1');
  }
  // For k=0 we only need H2..H_{2^{l-1}} (since we dispatch to Q_{2^l-1}).
  // For k>0 we additionally need H_{2^l}.
  if (k === 0) {
    if (Hs.length < l) {
      throw new Error(
        `Q_2lp1k_minus_1(k=0,l=${l}) requires Hs up to index ${l - 1} (H_{2^${l - 1}})`
      );
    }
  } else {
    if (Hs.length <= l) {
      throw new Error(`Q_2lp1k_minus_1 requires Hs up to index ${l} (H_{2^${l}})`);
    }
  }

  let deg = (1 << (l + 1)) * k + ((1 << l) - 1);
  if (deg === 0) {
    if (alpha.length !== 1) {
      throw new Error('degree-0 Q requires 1 parameter');
    }
    const z = AffineForm.const_only(field.coerce(alpha[0]));
    return [z, Hs.slice(), z];
  }

  if (alpha.length !== deg) {
    throw new Error(
      `Q_2lp1k_minus_1(k=${k},l=${l}) needs ${deg} alpha params, got ${alpha.length}`
    );
  }

  alpha = alpha.map((a) => field.coerce(a));

  if (k === 0) {
    // Q_{2^l-1} is the known-powers construction.
    const out = _paper_Q_known_powers(builder, l, alpha, Hs.slice(0, l));
    return [out, Hs.slice(), Hs[0]];
  }

  if (l === 1) {
    // Special case needed for the `8k+3` induction: build `Q_{4k+1}(x,H2)` from
    // `T_{2k,2}` using only a shifted quadratic input and a single top-level
    // `(x+β0)` extraction.
    //
    // Parameter layout (deg = 4k+1):
    //   - α0..α_{4k-3}   : T-params for `T_{2k,2}`
    //   - α_{4k-2}       : shift for `\tilde H2 = \hat H2 + α_{4k-2}`
    //   - α_{4k-1}       : quadratic shift `\hat H2 = H2 + α_{4k-1}`
    //   - α_{4k}         : extraction parameter `β0` in `(x+β0)S1 + S2`
    deg = 4 * k + 1;
    if (alpha.length !== deg) {
      throw new Error(
        `Q_2lp1k_minus_1(k=${k},l=1) needs ${deg} alpha params, got ${alpha.length}`
      );
    }
    if (Hs.length < 2) {
      throw new Error('Q_2lp1k_minus_1(l=1) requires Hs=[x,H2]');
    }
    alpha = alpha.map((a) => field.coerce(a));

    const t_params = alpha.slice(0, 4 * k - 2);
    const tilde_shift = alpha[4 * k - 2];
    const hat_shift = alpha[4 * k - 1];
    const beta0 = alpha[4 * k];

    const x = Hs[0];
    const H2 = Hs[1];
    const H_hat = H2.add_const(hat_shift, field);
    const tilde_H2 = H_hat.add_const(tilde_shift, field);

    const [S1, S2, Hs_out, tilde_out] = _paper_T(
      builder, 2 * k, 1, t_params, [x, H_hat], tilde_H2
    );
    const out = builder.mark_value(
      builder.mul(builder.x.add_const(beta0, field), S1).add(S2, field)
    );
    return [out, Hs_out, tilde_out];
  }

  const block = 1 << l;
  const a_alpha = alpha.slice(0, block - 2); // α0..α_{2^l-3}
  const t_start = block - 2;
  const shift_idx = (1 << (l + 1)) * k - 2; // α_{2^{l+1}k-2}
  const t_params = alpha.slice(t_start, shift_idx); // α_{2^l-2}..α_{2^{l+1}k-3}
  const shift = alpha[shift_idx];

  // Q_{2^{l-1}-1} parameters: length 2^{l-1}-1.
  // For l=1 this is 0, i.e. Q_0 is treated as the zero polynomial here.
  const qhat_start = shift_idx + 1;
  const qhat_len = (1 << (l - 1)) - 1;
  const qhat_params = alpha.slice(qhat_start, qhat_start + qhat_len);

  const beta_start = qhat_start + qhat_len;
  const beta_len = (1 << (l - 1)) + 1;
  const beta_params = alpha.slice(beta_start, beta_start + beta_len);
  if (beta_params.length !== beta_len || beta_start + beta_len !== alpha.length) {
    throw new Error('internal error: beta param count mismatch in Q_2lp1k_minus_1');
  }

  // \hat H_{2^l} = H_{2^l} + Q_{2^{l-1}-1}(qhat_params)
  let H_hat;
  if (l === 1) {
    H_hat = Hs[1];
  } else {
    const qhat = _paper_Q_known_powers(builder, l - 1, qhat_params, Hs.slice(0, l - 1));
    H_hat = Hs[l].add(qhat, field);
  }

  // Run T_{2k,2^l} with H_{2^l} replaced by \hat H_{2^l}.
  const Hs_hat = Hs.slice();
  Hs_hat[l] = H_hat;
  const need_t = (2 * k - 1) * block;
  if (t_params.length !== need_t) {
    throw new Error(`internal error: expected ${need_t} T-params, got ${t_params.length}`);
  }
  const [S1, S2, Hs_out, tilde_out] = _paper_T(
    builder, 2 * k, l, t_params, Hs_hat, H_hat.add_const(shift, field)
  );

  // Final fill: A_{2^{l-1}} on (S1,S2).
  const A_l = l - 1;
  const A_alpha_need = (1 << (A_l + 1)) - 2; // == 2^l - 2 (and 0 when l=1)
  if (a_alpha.length !== A_alpha_need) {
    throw new Error('internal error: A_alpha length mismatch in Q_2lp1k_minus_1');
  }

  const A_beta = []; // β0..β_{2^{l-1}}
  for (let i = 0; i < (1 << A_l) + 1; i++) A_beta.push(field.zero());
  for (let i = 0; i < beta_params.length; i++) {
    A_beta[(1 << A_l) - i] = beta_params[i];
  }

  const out = builder.mark_value(
    _paper_A_fill(builder, A_l, a_alpha.slice(), A_beta, S1, S2, Hs.slice(0, A_l + 1))
  );
  return [out, Hs_out, tilde_out];
}

// py: tools/poly_schedule.py:1297
// Concrete realization of the paper's "good polynomial" gadget \bar{Q}_deg.
//
// sections/constructions.tex only specifies how \bar{Q} is *used* (not its
// exact formula), but the surrounding text implies two requirements:
//   1) \bar{Q}_deg should be decodable given (H2,H4), and
//   2) it should fit the tight multiplication budget (deg//2 multiplications,
//      since (H2,H4) are treated as auxiliary wires).
//
// We implement the minimal family that matches these constraints:
//   - If deg = 4m+1:  \bar{Q}_{4m+1} := Q_{4m+1}(x,H2)  (the l=1 known-powers construction)
//   - If deg = 4m+3 (m>=1):
//         \bar{Q}_{4m+3} := (H2 + s) * Q_{4m+1}(x,H2) + (H4 + t)
//     which costs exactly one extra multiplication on top of Q_{4m+1} and uses
//     H4 only additively.
//
// Returns: [barQ, Hs_out] where Hs_out is Hs_in extended with any newly
// created "known powers" produced as byproducts of the internal Q_{4m+1} call.
function _paper_barQ_odd_with_H2_H4_with_powers(builder, deg, alpha, Hs_in) {
  const field = builder.field;
  if (deg < 1 || deg % 2 === 0) {
    throw new Error('barQ requires odd deg >= 1');
  }
  if (alpha.length !== deg) {
    throw new Error(`barQ_${deg} needs ${deg} alpha params, got ${alpha.length}`);
  }
  if (Hs_in.length < 2) {
    throw new Error('barQ requires Hs_in=[x,H2,...]');
  }

  alpha = alpha.map((a) => field.coerce(a));

  // Prefer the paper's known-powers `Q_deg` construction whenever the required
  // known powers are already available. This matches how \bar{Q} is used in
  // the induction steps: we thread through the byproduct powers from earlier
  // computations and use them when possible.
  const l_need = _v2_positive(deg + 1);
  const odd = (deg + 1) >> l_need;
  const kk = Math.floor((odd - 1) / 2);
  const need = kk > 0 ? l_need + 1 : l_need;
  if (Hs_in.length >= need) {
    const [q, Hs_out] = _paper_Q_for_odd_degree_with_powers(builder, deg, alpha, Hs_in);
    return [q, Hs_out];
  }

  if (Hs_in.length < 3) {
    throw new Error('barQ fallback requires H4 (Hs_in[2]) to be available');
  }
  const H2 = Hs_in[1];
  const H4 = Hs_in[2];

  // Keep the hand-crafted \bar{Q}_{15} used by the n=31 special case stable.
  if (deg === 15) {
    return [_paper_barQ_15(builder, alpha, H2, H4), Hs_in.slice()];
  }

  // Fallback for deg ≡ 7 (mod 8), i.e. deg = 8k+7 (k>=2 here since deg=15 is
  // handled above):
  //
  // Here v2(deg+1) >= 3, so the paper's `Q_deg` construction would require
  // higher known powers (H8/H16/...) that may not be available from earlier
  // steps. sections/constructions.tex instead assumes the existence of a "good
  // polynomial" gadget \bar{Q}_{4k+3} that is decodable given only (H2,H4).
  //
  // We realize the required instances using a tight-budget construction based
  // on the paper's own subroutines:
  //   - synthesize an H8 + \tilde H8,
  //   - run `T_{k,8}` to get a degree-(8k) compatible pair,
  //   - apply `A_4` to reach degree (8k+7).
  //
  // This keeps the Jacobian determinant constant and fits the exact (deg//2)
  // multiplication budget given (H2,H4).
  if (deg % 8 === 7 && deg >= 23) {
    const k = Math.floor((deg - 7) / 8);
    const [out, powers_out] = _paper_barQ_8k_plus_7_with_powers(builder, k, alpha, H2, H4);
    const Hs_out = Hs_in.slice();
    if (Hs_out.length < powers_out.length) {
      Hs_out.push(...powers_out.slice(Hs_out.length));
    }
    return [out, Hs_out];
  }

  throw new Error(
    `internal error: no barQ fallback case matched for deg=${deg} (need=${need}, have=${Hs_in.length})`
  );
}

// py: tools/poly_schedule.py:1381
function _paper_barQ_odd_with_H2_H4(builder, deg, alpha, H2, H4) {
  const [q] = _paper_barQ_odd_with_H2_H4_with_powers(builder, deg, alpha, [builder.x, H2, H4]);
  return q;
}

// py: tools/poly_schedule.py:1388
// Concrete construction for \bar{Q}_{15}(x,H2,H4) used in
// sections/constructions.tex (Special case 31).
//
// We implement `\bar{Q}_{15}` as a direct `A_4` (fill) instance, using only
// `H2` and `H4` plus one internally constructed monic degree-8 polynomial `H8`.
//
// Total multiplications given H2,H4: 1 (H8) + 6 (A_4) = 7.
function _paper_barQ_15(builder, alpha, H2, H4) {
  const field = builder.field;
  if (alpha.length !== 15) {
    throw new Error(`barQ_15 needs 15 parameters, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  const x = builder.x;

  // Parameter partition:
  //   - 3 params for H8: a,b,c
  //   - 1 param for shifting S2: d
  //   - 6 params for A_4 alpha: α0..α5
  //   - 5 params for A_4 beta:  β0..β4
  const a_h8 = alpha[0];
  const b_h8 = alpha[1];
  const c_h8 = alpha[2];
  const d_shift = alpha[3];

  const a_alpha = alpha.slice(4, 10);
  const beta = alpha.slice(10, 15);

  // H8 proxy (monic degree 8). We deliberately mix in both `x` and `H2` so the
  // low-degree part has enough structure for the downstream `A_4` fill.
  const A = x.add_const(b_h8, field); // degree 1
  const B = H2.add_const(c_h8, field); // degree 2
  builder.pushLabel('Q̄_15 block');
  const H8 = builder.withLabel('H_8 known power', () =>
    builder.mul(H4.add(A, field), H4.add(B, field))).add_const(a_h8, field);

  const S1 = H8;
  const S2 = H8.add_const(d_shift, field);
  const out = _paper_A_fill(builder, 2, a_alpha, beta, S1, S2, [x, H2, H4]);
  builder.popLabel();
  return out;
}

// py: tools/poly_schedule.py:1427
// Strong construction for \bar{Q}_{8k+7}(x,H2,H4) (k >= 2).
//
// This matches the "\bar Q only needs (H2,H4)" assumption in the induction
// steps, while keeping the Jacobian determinant constant.
//
// Structure (tight multiplication budget):
//   - Build a monic degree-8 power H8 and a shifted \tilde H8.
//   - Use `T_{k,8}` (Algorithm 3) to obtain a degree-(8k) compatible pair.
//   - Apply `A_4` (i.e. `A_fill(l=2)`) to reach degree (8k+7).
//
// Parameter partition (8k+7 total):
//   - 4 params for (H8, \tilde H8): a,b,c,d
//   - (k-1)*8 params for T_{k,8}
//   - 11 params for A_4 (6 alpha + 5 beta)
function _paper_barQ_8k_plus_7_with_powers(builder, k, alpha, H2, H4) {
  const field = builder.field;
  if (k < 2) {
    throw new Error('barQ_{8k+7} requires k>=2');
  }
  const deg = 8 * k + 7;
  if (alpha.length !== deg) {
    throw new Error(`barQ_{8k+7} (k=${k}) needs ${deg} parameters, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  const x = builder.x;

  const [a_h8, b_h8, c_h8, d_tilde] = alpha.slice(0, 4);
  const t_len = (k - 1) * 8;
  const t_params = alpha.slice(4, 4 + t_len);
  const fill = alpha.slice(4 + t_len);
  const a_alpha = fill.slice(0, 6);
  const beta = fill.slice(6);
  if (t_params.length !== t_len || a_alpha.length !== 6 || beta.length !== 5) {
    throw new Error('internal error: barQ_{8k+7} parameter partition mismatch');
  }

  // H8 proxy (monic degree 8) + tilde shift.
  builder.pushLabel(`Q̄_${deg} block (8k+7, k=${k})`);
  const H8 = builder.withLabel('H_8 known power', () => builder.mul(
    H4.add(x.add_const(b_h8, field), field),
    H4.add(H2.add_const(c_h8, field), field)
  )).add_const(a_h8, field);
  const tilde_H8 = H8.add_const(d_tilde, field);

  // Degree-(8k) compatible pair from T_{k,8}.
  const [S1, S2, Hs_out, _tilde_out] = _paper_T(
    builder, k, 3, t_params, [x, H2, H4, H8], tilde_H8
  );

  // Final A_4 fill adds 7 degrees: 8k -> 8k+7.
  const out = _paper_A_fill(builder, 2, a_alpha, beta, S1, S2, [x, H2, H4]);
  builder.popLabel();

  // Expose any higher known powers produced by the internal T recursion.
  return [out, Hs_out.slice()];
}

// py: tools/poly_schedule.py:1546
// Build (T^{(1)}_n, T^{(2)}_n) and return a byproduct list of "known powers".
//
// This implements the casework / induction steps in sections/constructions.tex,
// plus the explicit special cases 15/27/31.
//
// Return value:
//   - [T1, T2, Hs] where Hs[i] is a monic degree-2^i polynomial ("known power"),
//     with Hs[0]=x. (We do not enforce that these are literal iterated squares;
//     the paper's constructions only require the degree/monicity structure.)
function _paper_splittable_pair(builder, n, alpha) {
  // JS-only provenance wrapper: the pair (T^(1)_n, T^(2)_n) with P = x·T^(1) + T^(2).
  return builder.withLabel(`splittable pair (T⁽¹⁾_${n}, T⁽²⁾_${n})`, () =>
    _paper_splittable_pair_impl(builder, n, alpha));
}

function _paper_splittable_pair_impl(builder, n, alpha) {
  const field = builder.field;
  if (n < 1 || n % 2 === 0) {
    throw new Error('splittable_pair requires odd n >= 1');
  }
  if (n === 7) {
    throw new Error('no splittable pair is used for n=7; use the septic base construction instead');
  }
  if (alpha.length !== n) {
    throw new Error(`splittable_pair(${n}) needs ${n} params, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  // Tiny bases.
  if (n === 1) {
    const x = builder.x;
    return [builder.const(field.one()), builder.const(alpha[0]), [x]];
  }

  if (n === 3) {
    // H2 = (x + α2)x + α1
    // T1 = H2, T2 = H2 + α0
    const x = builder.x;
    const H2 = _paper_H2(builder, alpha[1], alpha[2]);
    return [H2, H2.add_const(alpha[0], field), [x, H2]];
  }

  // Explicit special cases from sections/constructions.tex.
  if (n === 15) {
    const H2 = _paper_H2(builder, alpha[6], alpha[7]);
    const x = builder.x;
    const x_shift = x.add_const(alpha[5], field);
    const H4 = builder.withLabel('H_4 known power', () =>
      _paper_square_diff(builder, H2, x_shift)).add_const(alpha[4], field);

    const S1 = _paper_Q_known_powers(builder, 3, alpha.slice(8, 15), [x, H2, H4]);
    const S2 = H2.add_const(alpha[3], field);
    const T1 = _paper_square_diff(builder, S1, S2).add_const(alpha[1], field);

    // sections/constructions.tex defines
    //   T2_low = H4^2 - (H2+α2)^2 + α0
    // which has degree 8. For the later induction steps we need the second
    // component to have degree 14. We "promote" it by adding `T1` (no extra
    // multiplications), mirroring the fix used in the `n=27` special case.
    const T2_low = _paper_square_diff(builder, H4, H2.add_const(alpha[2], field))
      .add_const(alpha[0], field);
    const T2 = T2_low.add(T1, field);
    // Expose the monic degree-8 byproduct (used as H8 in the 8k+7 induction).
    const H8 = T2_low;
    return [T1, T2, [x, H2, H4, H8]];
  }

  if (n === 27) {
    const H2 = _paper_H2(builder, alpha[2], alpha[3]);
    const x = builder.x;

    // Special case 27 from sections/constructions.tex.
    //
    // Note: sections/constructions.tex writes `T^{(2)}_{27}` as a low-degree
    // (deg 14) expression. That version is bijective by itself, but it does not
    // compose correctly as a "splittable pair" inside the later `8k+3` induction.
    //
    // We repair it by following the same template as the `n=31` special case:
    // use the *same* high-degree polynomial (`Q13`) in both components, but
    // introduce an external shift (here we reuse `α13`, which is not used by
    // `Q13`) so the map remains generically invertible.
    const [S1, Hs_out] = _paper_Q_2lp1k_minus_1_with_powers(
      builder, 3, 1, alpha.slice(14, 27), [x, H2]
    );
    if (Hs_out.length <= 2) {
      throw new Error('internal error: expected H4 byproduct in Q_13');
    }
    const H4 = Hs_out[2];
    const Hs = [x, H2].concat(Hs_out.slice(2));

    const S2 = _paper_q3(builder, alpha[4], alpha[5], alpha[6], H2);
    const S3 = _paper_Q_known_powers(builder, 3, alpha.slice(7, 14), [x, H2, H4]);

    const T1 = _paper_square_diff(builder, S1, S2).add_const(alpha[1], field);
    // Promote the low-degree second component by adding `T1` (no extra multiplications).
    // This yields a degree-26 `T2` that composes correctly in later induction steps.
    const T2_low = _paper_square_diff(builder, S3, H2).add_const(alpha[0], field);
    const T2 = T2_low.add(T1, field);
    return [T1, T2, Hs];
  }

  if (n === 31) {
    const H2 = _paper_H2(builder, alpha[6], alpha[7]);
    const x = builder.x;
    const x_shift = x.add_const(alpha[5], field);
    const H4 = builder.withLabel('H_4 known power', () =>
      _paper_square_diff(builder, H2, x_shift)).add_const(alpha[4], field);

    // sections/constructions.tex (Special case 31) references a "good polynomial"
    // gadget \bar{Q}_{15}(x,H2,H4).
    const S1 = _paper_barQ_odd_with_H2_H4(builder, 15, alpha.slice(16, 31), H2, H4);
    const S2 = _paper_Q_known_powers(builder, 3, alpha.slice(8, 15), [x, H2, H4]);
    const S3 = _paper_q3(builder, alpha[1], alpha[2], alpha[3], H2);
    const T1 = _paper_square_diff(builder, S1, S2).add(S3, field);

    const T2 = _paper_square_diff(builder, S1.add_const(alpha[15], field), H4)
      .add_const(alpha[0], field);
    return [T1, T2, [x, H2, H4]];
  }

  // Main families / induction steps.
  if (n % 4 === 1) {
    // n = 4k+1
    const k = Math.floor((n - 1) / 4);
    // Paper indexing/layout (sections/constructions.tex, Lemma "The 4k+1 family
    // is splittable"):
    //   - α0..α_{4k-3}   : parameters for the internal `T_{2k,2}` call
    //   - α_{4k-2}       : scalar shift in \tilde H2 = H2 + α_{4k-2}
    //   - α_{4k-1},α_{4k}: H2 = (x + α_{4k})x + α_{4k-1}
    //
    // This "high-indexed H2" convention is important for the paper-faithful
    // coefficient→parameter decoding algorithms, which recover H2 from the
    // top coefficients of P_{4k+1}.
    const t_params = alpha.slice(0, n - 3);
    const tilde_shift = alpha[n - 3];
    const h2_const = alpha[n - 2];
    const h2_lin = alpha[n - 1];

    const H2 = _paper_H2(builder, h2_const, h2_lin);
    const tilde_H2 = H2.add_const(tilde_shift, field);
    const x = builder.x;
    const [T1, T2, Hs_out, _tilde_out] = _paper_T(
      builder, 2 * k, 1, t_params, [x, H2], tilde_H2
    );
    // Keep the "known powers" produced by the internal T recursion.
    return [T1, T2, Hs_out];
  }

  if (n % 8 === 3) {
    // n = 8k+3 (k>=1 here; n=3 handled above)
    const k = Math.floor((n - 3) / 8);
    const sub_n = 2 * k + 1;
    const [S1_1, S1_2, Hs] = _paper_splittable_pair(builder, sub_n, alpha.slice(2 * k, 4 * k + 1));
    if (Hs.length < 2) {
      throw new Error('internal error: expected H2 in splittable_pair output');
    }
    const x = Hs[0];
    const H2 = Hs[1];

    // Paper induction step (sections/constructions.tex, Algorithm "If 2k+1 is
    // splittable then 8k+3 is splittable"):
    //   S2 = Q_{4k+1}(x,H2), which also makes an H4 derivable as a byproduct.
    const [S2, Hs2_raw, _tilde_out] = _paper_Q_2lp1k_minus_1_with_powers(
      builder, k, 1, alpha.slice(4 * k + 2, 8 * k + 3), [x, H2]
    );
    if (Hs2_raw.length <= 2) {
      throw new Error('internal error: expected an H4 byproduct in Q_{4k+1}');
    }

    // The l=1 Q_{4k+1} construction internally shifts H2 to \hat H2; the
    // known-powers byproducts beyond H2 are still valid, but we must keep
    // the original H2 at Hs[1] for downstream Q calls.
    let Hs2 = [x, H2].concat(Hs2_raw.slice(2));

    // S3 = Q_{2k-1}(x, H2, H4, ..., H_{2^ℓ}).
    //
    // sections/constructions.tex special-cases k=1 (so 2k-1=1) and simply uses
    // the constant α1 instead of the generic Q_1 gadget.
    let S3;
    let Hs3;
    if (k === 1) {
      S3 = builder.const(alpha[1]);
      Hs3 = Hs2.slice();
    } else {
      const deg3 = 2 * k - 1;
      [S3, Hs3] = _paper_Q_for_odd_degree_with_powers(builder, deg3, alpha.slice(1, 2 * k), Hs2);
    }

    // Preserve any higher "known powers" produced by the recursive S1 call,
    // and extend with any additional byproducts from S3.
    if (Hs.length > Hs2.length) {
      Hs2 = Hs2.slice().concat(Hs.slice(Hs2.length));
    }
    if (Hs3.length > Hs2.length) {
      Hs2 = Hs2.slice().concat(Hs3.slice(Hs2.length));
    }

    const T1 = _paper_square_diff(builder, S2, S1_1).add(S3, field);
    const T2 = _paper_square_diff(builder, S2.add_const(alpha[4 * k + 1], field), S1_2)
      .add_const(alpha[0], field);
    // Expose the "known powers" computed while building S2; higher-level calls
    // may need H8/H16/... (e.g. when a later Q-construction has v2(deg+1) >= 3).
    return [T1, T2, Hs2];
  }

  if (n % 8 === 7) {
    // n = 8k+7 (n in {7,15,31} handled above)
    const k = Math.floor((n - 7) / 8);
    const sub_n = 2 * k + 1;
    let [S1_1, S1_2, Hs] = _paper_splittable_pair(builder, sub_n, alpha.slice(0, 2 * k + 1));
    if (Hs.length < 2) {
      throw new Error('internal error: expected H2 in splittable_pair output for 8k+7 case');
    }
    let H2 = Hs[1];

    // Build the Q_deg polynomial needed by the `8k+7` induction.
    //
    // We prefer the paper's "known powers" Q construction whenever the required
    // known powers are already available from earlier steps (either from the
    // recursive splittable-pair call or produced as byproducts of prior Q calls).
    //
    // If the required powers are *not* available, we must not synthesize them
    // with extra squarings (that would exceed the n/2+1 multiplication budget).
    // In that case we fall back to the `\bar Q` gadget family, which is designed
    // to work using only (H2,H4) as auxiliary inputs.
    function build_Q(deg, params, Hs_in) {
      const l = _v2_positive(deg + 1);
      const odd = (deg + 1) >> l;
      const kk = Math.floor((odd - 1) / 2);
      const need = kk > 0 ? l + 1 : l;

      // If we have enough known powers, use the paper's `Q_deg` construction.
      if (Hs_in.length >= need) {
        const [q, Hs_out] = _paper_Q_for_odd_degree_with_powers(builder, deg, params, Hs_in);
        return [q, Hs_out];
      }

      // Otherwise, fall back to the "good polynomial" gadget family \bar{Q}_deg
      // which is designed to work with only (H2,H4) as auxiliary inputs.
      const [q, Hs_out] = _paper_barQ_odd_with_H2_H4_with_powers(builder, deg, params, Hs_in);
      return [q, Hs_out];
    }

    // S2 = Q_{2k+1}[…], and keep any newly produced known powers.
    let res = build_Q(sub_n, alpha.slice(2 * k + 2, 4 * k + 3), Hs);
    const S2 = res[0];
    Hs = res[1];
    if (Hs.length < 2) {
      throw new Error('internal error: expected H2 to remain available after Q_{2k+1}');
    }
    H2 = Hs[1];

    // S3 = Q_{4k+3}[…], which may require more known powers than S1 produced.
    res = build_Q(4 * k + 3, alpha.slice(4 * k + 4, 8 * k + 7), Hs);
    const S3 = res[0];
    Hs = res[1];

    const T1 = _paper_square_diff(builder, S3, S2).add(S1_1, field);

    const S2_shift = S2.add_const(alpha[2 * k + 1], field);
    const S3_shift = S3.add_const(alpha[4 * k + 3], field);
    const T2 = _paper_square_diff(builder, S3_shift, S2_shift).add(S1_2, field);
    return [T1, T2, Hs];
  }

  throw new Error(`internal error: no splittable case matched for odd n=${n}`);
}

// py: tools/poly_schedule.py:6921
// Compile the paper's parameterized polynomial family `P_n[α0..α_{n-1}]` into
// a chain.
//
// This is the forward (evaluation) direction: it does *not* implement the
// coefficient → parameter decoding step from the notes.
// (JS port: `modulus` is a BigInt prime, null (exact rationals — the Python
// float check is dropped), or a ready-made field object exposing the Field
// interface (coerce/add/mul/…), e.g. the website's double-precision field.)
function compile_paper_params_chain(params, modulus = null) {
  const params_list_in = Array.from(params);
  if (params_list_in.length === 0) {
    throw new Error('params must be non-empty');
  }

  const field = (modulus !== null && typeof modulus === 'object' && typeof modulus.coerce === 'function')
    ? modulus : new Field({ modulus });
  const params_list = params_list_in.map((a) => field.coerce(a));

  const n = params_list.length;
  const builder = new ChainBuilder(field);

  function build_P(deg, a) {
    if (deg !== a.length) {
      throw new Error('internal error: parameter length mismatch in build_P');
    }
    if (deg === 1) {
      return builder.x.add_const(a[0], field);
    }
    if (deg === 5) {
      return _paper_P5(builder, a);
    }
    if (deg === 7) {
      const two = field.add(field.one(), field.one());
      if (field.is_zero(two)) {
        // py: return _paper_P7_char2(builder, a) — char-2 lane not ported.
        throw new Error('_paper_P7_char2 is not ported (characteristic-2 branch)');
      }
      return _paper_P7(builder, a);
    }
    if (deg % 2 === 0) {
      const q = build_P(deg - 1, a.slice(1));
      return builder.withLabel(`even lift P_${deg} = x·P_${deg - 1} + α_0`, () =>
        builder.mul(q, builder.x)).add_const(a[0], field);
    }

    const [T1, T2, _H2] = _paper_splittable_pair(builder, deg, a);
    return builder.withLabel(`P_${deg} = x·T⁽¹⁾ + T⁽²⁾`, () =>
      builder.mul(T1, builder.x)).add(T2, field);
  }

  const out = build_P(n, params_list);
  const chain = builder.finalize(out);
  chain.validate();
  return chain;
}

// ====================================================================
// BEGIN g7_polychain.frag.js
// ====================================================================
// g7_polychain.frag.js — polychain spine (tools/polychain.py) for the char-0
// lane port.  Fragment: function declarations only (plus the MERSENNE61
// constant); no imports/exports, no top-level side effects.  All ps.* names
// from the Python are bare names here — other fragments supply them.

// py: tools/polychain.py:61
const MERSENNE61 = (1n << 61n) - 1n;

// =============================================================================
// Fields
// =============================================================================

// py: tools/polychain.py:69
// The prime field GF(p) (odd p; characteristic 2 is rejected at decode time).
// JS: p may be a Number or a BigInt; the Field stores the modulus as BigInt.
function GF(p) {
  return new Field({ modulus: BigInt(p) });
}

// py: tools/polychain.py:75
// Exact rational arithmetic (Python `fractions.Fraction` -> Rat).
// (Python passes use_fractions=True; in this port modulus=null implies it.)
function rationals() {
  return new Field({ modulus: null });
}

// py: tools/polychain.py:81
function default_field() {
  return GF(MERSENNE61);
}

// py: tools/polychain.py:85
function _require_odd_characteristic(field, purpose) {
  if (field.modulus === 2n) {
    throw new Error(
      `${purpose} over characteristic 2 is not supported by polychain; ` +
      "see poly_schedule's char-2 septic base for the GF(2^k) constructions"
    );
  }
}

// =============================================================================
// Encoding (coefficient expansion of P_n[α])
// =============================================================================

// py: tools/polychain.py:98
// Expand P_n[α_0..α_{n-1}] and return its non-leading coefficients
// [c_0, ..., c_{n-1}]  (the polynomial is x^n + Σ_j c_j x^j).
//
// With peeled=true the known-powers gadgets Q_{2^k-1} use the depth-balanced
// peeled recursion (same multiplications and additions, height O(log n)
// overall); the parameter layout inside those blocks changes accordingly.
function encode(n, alphas, field = null, { peeled = false } = {}) {
  field = field || default_field();
  if (peeled) {
    return _with_peeled(() => encode(n, alphas, field));
  }
  if (n < 1) {
    throw new Error('encode requires n >= 1');
  }
  alphas = alphas.map((a) => field.coerce(a));
  if (alphas.length !== n) {
    throw new Error(`P_${n} takes exactly ${n} parameters, got ${alphas.length}`);
  }
  let P = _poly_paper_P_from_params({ params: alphas, field });
  P = _poly_trim(P, field);
  if (_poly_degree(P) !== n || !field.eq(P[P.length - 1], field.one())) {
    throw new Error('internal error: encoder did not produce a monic degree-n polynomial');
  }
  return P.slice(0, n);
}

// =============================================================================
// Decoding (rational preprocessing: coefficients -> parameters)
// =============================================================================

// py: tools/polychain.py:130
// Invert `encode`: given the coefficients c_0..c_{n-1} of the monic
// polynomial x^n + Σ_j c_j x^j, return parameters α_0..α_{n-1} with
// P_n[α] equal to that polynomial.  The result is verified by re-expansion.
//
// Mirrors `alg:final-decoder` in sections/constructions.tex.
function decode(n, coeffs, field = null, { peeled = false } = {}) {
  field = field || default_field();
  if (peeled) {
    return _with_peeled(() => decode(n, coeffs, field));
  }
  _require_odd_characteristic(field, 'decoding');
  if (n < 1) {
    throw new Error('decode requires n >= 1');
  }
  let cs = coeffs.map((c) => field.coerce(c));
  if (cs.length === n + 1) {
    if (!field.eq(cs[cs.length - 1], field.one())) {
      throw new Error('decode expects a monic polynomial (leading coefficient 1)');
    }
    cs = cs.slice(0, n);
  }
  if (cs.length !== n) {
    throw new Error(`decode of degree ${n} needs ${n} coefficients c_0..c_${n - 1}, got ${cs.length}`);
  }
  const full = cs.concat([field.one()]);

  const alphas = _decode_monic(full, field);

  const check = _poly_trim(_poly_paper_P_from_params({ params: alphas, field }), field);
  if (!_poly_eq(check, _poly_trim(full, field), field)) {
    throw new Error(`decode(n=${n}): parameters failed re-expansion verification`);
  }
  return alphas;
}

// py: tools/polychain.py:163
// Even lift P_n = α_0 + x·P_{n-1}, then odd-degree dispatch.
function _decode_monic(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  const n = _poly_degree(coeffs);
  if (n < 1) {
    throw new Error('polynomial must have positive degree');
  }
  if (!field.eq(coeffs[coeffs.length - 1], field.one())) {
    throw new Error('decode expects a monic polynomial');
  }
  if (n % 2 === 0) {
    return [coeffs[0]].concat(_decode_monic(coeffs.slice(1), field));
  }
  return _decode_odd(coeffs, field, { pair_context: false });
}

// py: tools/polychain.py:177
// Decode odd-degree P_n = x·T^{(1)}_n + T^{(2)}_n.
//
// `pair_context` selects the splittable-pair parameterization for n=5
// (used as the inner block of the 8k+7 step), which differs from the
// top-level P_5 base construction.  n=7 never occurs as an inner block
// (k=3 instances are the special cases 27 and 31).
function _decode_odd(coeffs, field, { pair_context }) {
  coeffs = _poly_trim(coeffs, field);
  const n = _poly_degree(coeffs);
  if (n === 1) {
    return [coeffs[0]];
  }
  if (pair_context && n === 5) {
    // Splittable pair for 5 = k=1 instance of the 4k+1 family.
    function enc5(a) {
      const [T1, T2] = _poly_paper_splittable_pair({ n: 5, alpha: a.slice(), field });
      return _poly_add(_poly_shift_xk(T1, 1, field), T2, field);
    }

    return _decode_by_descending_pivots({
      target: coeffs, encode_fn: enc5, nparams: 5, field, what: 'pair(5)',
    });
  }
  if (pair_context && n === 7) {
    throw new Error('internal error: no splittable pair exists for 7');
  }
  if ([3, 5, 7, 11, 15].includes(n) || n % 4 === 1) {
    // Bases, the 4k+1 family (lem:4k+1-splittable + alg:decode-Rk2l),
    // and the specials 11/15 — all implemented in poly_schedule.
    return _decode_P_coeffs_to_paper_params(coeffs, field);
  }
  if (n === 27) {
    return _decode_pair_27(coeffs, field);
  }
  if (n === 31) {
    return _decode_pair_31(coeffs, field);
  }
  if (n % 8 === 3) {
    return _decode_pair_8k3(coeffs, field);
  }
  if (n % 8 === 7) {
    return _decode_pair_8k7(coeffs, field);
  }
  throw new Error(`internal error: no decoding family matched odd n=${n}`);
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

// py: tools/polychain.py:222
function _x(field) {
  return [field.zero(), field.one()];
}

// py: tools/polychain.py:226
// x·S^2 + (S+δ)^2 (the square gadget of `lem:square-gadget`).
function _square_gadget_poly(S, delta, field) {
  const S_sq = _poly_square(S, field);
  const shifted = _poly_square(_poly_add_const(S, delta, field), field);
  return _poly_add(_poly_shift_xk(S_sq, 1, field), shifted, field);
}

// py: tools/polychain.py:234
// Divide by x, requiring a zero constant term is NOT required (drop it).
function _shift_down(p, field) {
  return _poly_trim(p.slice(1), field);
}

// py: tools/polychain.py:240
// Mirror of the encoder's `build_Q` in `_poly_paper_splittable_pair` (8k+7
// branch): the odd-degree known-powers gadget when enough powers are
// available, the bar-Q fallback otherwise.  Returns [encode_fn, hs_out_fn].
function _build_Q_encoder(deg, Hs_in, field) {
  const l = _v2_positive(deg + 1);
  const odd = (deg + 1) >> l;
  const kk = Math.floor((odd - 1) / 2);
  const need = kk > 0 ? l + 1 : l;
  if (Hs_in.length >= need) {
    function enc(a) {
      const [q] = _poly_paper_Q_for_odd_degree_with_powers({
        deg, alpha: a.slice(), Hs: Hs_in, field,
      });
      return _poly_trim(q, field);
    }

    function hs_out(a) {
      const [, hs] = _poly_paper_Q_for_odd_degree_with_powers({
        deg, alpha: a.slice(), Hs: Hs_in, field,
      });
      return hs.slice();
    }

    return [enc, hs_out];
  } else {
    function enc(a) {
      const [q] = _poly_paper_barQ_odd_with_H2_H4_with_powers({
        deg, alpha: a.slice(), Hs_in, field,
      });
      return _poly_trim(q, field);
    }

    function hs_out(a) {
      const [, hs] = _poly_paper_barQ_odd_with_H2_H4_with_powers({
        deg, alpha: a.slice(), Hs_in, field,
      });
      return hs.slice();
    }

    return [enc, hs_out];
  }
}

// py: tools/polychain.py:278
// Parameter block of Q_{4k+1}(x, H_2) (lem:Q4k+1-from-H2) by descending pivots.
function _solve_Q4kp1(target, kk, H2, field) {
  const x = _x(field);

  function enc(av) {
    const [q] = _poly_paper_Q_2lp1k_minus_1_with_powers({
      k: kk, l: 1, alpha: av.slice(), Hs: [x, H2], field,
    });
    return _poly_trim(q, field);
  }

  return _decode_by_descending_pivots({
    target, encode_fn: enc, nparams: 4 * kk + 1, field, what: `Q_{${4 * kk + 1}} given H2`,
  });
}

// py: tools/polychain.py:294
// Known-power byproducts [x, H_2, H_4, ...] of a Q_{4k+1}(x,H_2) instance.
function _Q4kp1_powers(params, kk, H2, field) {
  const x = _x(field);
  const [, hs_raw] = _poly_paper_Q_2lp1k_minus_1_with_powers({
    k: kk, l: 1, alpha: params.slice(), Hs: [x, H2], field,
  });
  return [x, H2].concat(hs_raw.slice(2));
}

// py: tools/polychain.py:304
// Parameter block of the odd-degree known-powers gadget Q_deg (lem:Q-odd-degree-with-powers).
function _solve_Qodd(target, deg, Hs, field) {
  function enc(av) {
    const [q] = _poly_paper_Q_for_odd_degree_with_powers({ deg, alpha: av.slice(), Hs, field });
    return _poly_trim(q, field);
  }

  return _decode_by_descending_pivots({
    target, encode_fn: enc, nparams: deg, field, what: `Q_{${deg}} with powers`,
  });
}

// py: tools/polychain.py:316
// [α_4, α_5, α_6, α_7] from H_4 = H_2² − (x+α_5)² + α_4, H_2 = x² + α_7 x + α_6.
function _h4_block_params(H4, field) {
  const one = field.one();

  function enc(a) {
    const H2 = [a[2], a[3], one];
    return _poly_add_const(
      _poly_sub(_poly_square(H2, field), _poly_square([a[1], one], field), field),
      a[0],
      field
    );
  }

  return _decode_by_descending_pivots({ target: H4, encode_fn: enc, nparams: 4, field, what: 'H4 block' });
}

// py: tools/polychain.py:332
// Closed-form chain for P3 = −(x+1)·Q_3² + (x+1)·α_1 − H_2² + α_0 with
// Q_3 = x³+γ₂x²+γ₁x+γ₀ = Q_3[α_4,α_5,α_6](x,H_2) and H_2 = x²+bx+c
// (b = α_3, c = α_2).  Returns [α_0, ..., α_6].
function _decode_27_low_block(P3, field) {
  const one = field.one();
  const inv2 = field.inv(field.add(one, one));
  const c_ = (j) => _poly_coeff(P3, j, field);
  const mul = (u, v) => field.mul(u, v);
  const add = (u, v) => field.add(u, v);
  const sub = (u, v) => field.sub(u, v);
  const neg = (u) => field.neg(u);

  function dbl(v) {
    return add(v, v);
  }

  const g2 = mul(sub(neg(c_(6)), one), inv2);                        // P3_6 = −(2γ₂ + 1)
  const q5 = dbl(g2);                                                // [x^5]Q_3²
  const g1 = mul(sub(sub(neg(c_(5)), mul(g2, g2)), q5), inv2);       // P3_5 = −(γ₂²+2γ₁ + q5)
  const q4 = add(mul(g2, g2), dbl(g1));
  const g0 = mul(sub(sub(sub(neg(c_(4)), one), dbl(mul(g2, g1))), q4), inv2);  // P3_4 = −(2γ₀+2γ₂γ₁ + q4) − 1
  const q3 = add(dbl(g0), dbl(mul(g2, g1)));
  const q2 = add(mul(g1, g1), dbl(mul(g2, g0)));
  const b = mul(sub(sub(neg(c_(3)), q2), q3), inv2);                 // P3_3 = −(q2+q3) − 2b
  const q1 = dbl(mul(g1, g0));
  const c = mul(sub(sub(sub(neg(c_(2)), q1), q2), mul(b, b)), inv2); // P3_2 = −(q1+q2) − (b²+2c)
  const q0 = mul(g0, g0);
  const alpha1 = add(add(add(c_(1), q0), q1), dbl(mul(b, c)));       // P3_1 = −(q0+q1) + α_1 − 2bc
  const alpha0 = add(sub(add(c_(0), q0), alpha1), mul(c, c));        // P3_0 = −q0 + α_1 + α_0 − c²

  const alpha6 = sub(g2, b);                                         // γ₂ = b + α_6
  const alpha5 = sub(sub(g1, c), mul(alpha6, b));                    // γ₁ = c + α_5 + α_6 b
  const alpha4 = sub(g0, mul(alpha6, add(c, alpha5)));               // γ₀ = α_6 (c + α_5) + α_4
  return [alpha0, alpha1, c, b, alpha4, alpha5, alpha6];
}

// ---------------------------------------------------------------------------
// Inner pair from its squares: Ψ = x·T1² + T2²  (lem:compatible-power)
// ---------------------------------------------------------------------------
//
// The 8k+3 step exposes the inner splittable pair (T1, T2) only through
// Ψ = x·T1² + T2² on the degrees >= deg T1.  The paper recovers the pair via
// the square-closure certificate; numerically we solve the map vals -> Ψ by
// descending affine pivots after *re-parameterizing* the pair: every
// Q-sub-block is replaced by its free polynomial coefficients (the known-powers
// Q maps are coefficient-bijective by lem:Q-unitriangular), recursively through
// the family tree.  In these coordinates each unknown first appears affinely
// with a constant slope, so `_decode_by_descending_pivots` applies; the actual
// parameter blocks are then extracted from the recovered sub-polynomials by the
// same Q-decoders the top-level families use.

// py: tools/polychain.py:383
function _pairsq_psi(T1, T2, field) {
  return _poly_add(_poly_shift_xk(_poly_square(T1, field), 1, field), _poly_square(T2, field), field);
}

// py: tools/polychain.py:387
// Free-coordinate parameterization of the splittable pair for odd m.
//
// Returns [nvals, build, extract] with build(vals) -> [T1, T2] and
// extract(vals) -> the paper parameter block α' (extract runs the
// appropriate Q-block decoders on the recovered free polynomials).
function _pair_free(m, field) {
  const one = field.one();
  const sq = (p) => _poly_square(p, field);
  const add = (p, q) => _poly_add(p, q, field);
  const sub = (p, q) => _poly_sub(p, q, field);
  const addc = (p, c) => _poly_add_const(p, c, field);

  if (m <= 5 || m % 4 === 1) {
    // The T-tower families are descending-triangular in their own
    // parameters (cf. the pivot tables of lem:4k+1-splittable / lem:Rk2l).
    function build(vals) {
      const [T1, T2] = _poly_paper_splittable_pair({ n: m, alpha: vals.slice(), field });
      return [T1, T2];
    }

    return [m, build, (vals) => vals.slice()];
  }

  if (m === 15) {
    // [α0..α7 | S free(7)] with S = Q7(x,H2,H4).
    function build(vals) {
      const a8 = vals.slice(0, 8);
      const S = vals.slice(8, 15).concat([one]);
      const H2 = [a8[6], a8[7], one];
      const H4 = addc(sub(sq(H2), sq([a8[5], one])), a8[4]);
      const T1 = addc(sub(sq(S), sq(addc(H2, a8[3]))), a8[1]);
      const T2 = addc(add(T1, sub(sq(H4), sq(addc(H2, a8[2])))), a8[0]);
      return [T1, T2];
    }

    function extract(vals) {
      const H2 = [vals[6], vals[7], one];
      const H4 = addc(sub(sq(H2), sq([vals[5], one])), vals[4]);
      const S = _poly_trim(vals.slice(8, 15).concat([one]), field);
      const q7 = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
        Q: S, k: 3, Hs: [_x(field), H2, H4], field,
      });
      return vals.slice(0, 8).concat(q7);
    }

    return [15, build, extract];
  }

  if (m === 27) {
    // [α0, α1, α2, α3 | Q3 free(3) | S3 free(7) | S1 free(13)].
    function build(vals) {
      const H2 = [vals[2], vals[3], one];
      const q3 = vals.slice(4, 7).concat([one]);
      const S3 = vals.slice(7, 14).concat([one]);
      const S1 = vals.slice(14, 27).concat([one]);
      const T1 = addc(sub(sq(S1), sq(q3)), vals[1]);
      const T2 = add(T1, addc(sub(sq(S3), sq(H2)), vals[0]));
      return [T1, T2];
    }

    function extract(vals) {
      const H2 = [vals[2], vals[3], one];
      const q3poly = _poly_trim(vals.slice(4, 7).concat([one]), field);
      const S3poly = _poly_trim(vals.slice(7, 14).concat([one]), field);
      const S1poly = _poly_trim(vals.slice(14, 27).concat([one]), field);
      const q3block = _decode_Q3_coeffs_to_alpha_given_H2(q3poly, H2, field);
      const q13 = _solve_Q4kp1(S1poly, 3, H2, field);
      const H4 = _Q4kp1_powers(q13, 3, H2, field)[2];
      const q7 = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
        Q: S3poly, k: 3, Hs: [_x(field), H2, H4], field,
      });
      return [vals[0], vals[1], vals[2], vals[3]].concat(q3block, q7, q13);
    }

    return [27, build, extract];
  }

  if (m === 31) {
    // [α0 | Q3 free(3) | H4 free(4) | S2 free(7) | α15 | S1 free(15)].
    function build(vals) {
      const S3q = vals.slice(1, 4).concat([one]);
      const H4 = vals.slice(4, 8).concat([one]);
      const S2 = vals.slice(8, 15).concat([one]);
      const a15 = vals[15];
      const S1 = vals.slice(16, 31).concat([one]);
      const T1 = add(sub(sq(S1), sq(S2)), S3q);
      const T2 = addc(sub(sq(addc(S1, a15)), sq(H4)), vals[0]);
      return [T1, T2];
    }

    function extract(vals) {
      const S3q = _poly_trim(vals.slice(1, 4).concat([one]), field);
      const H4 = _poly_trim(vals.slice(4, 8).concat([one]), field);
      const S2 = _poly_trim(vals.slice(8, 15).concat([one]), field);
      const S1 = _poly_trim(vals.slice(16, 31).concat([one]), field);
      const a47 = _h4_block_params(H4, field);
      const H2 = [a47[2], a47[3], one];
      const q3 = _decode_Q3_coeffs_to_alpha_given_H2(S3q, H2, field);
      const q7 = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
        Q: S2, k: 3, Hs: [_x(field), H2, H4], field,
      });

      function enc_bar(a) {
        return _poly_trim(_poly_paper_barQ_15({ alpha: a.slice(), H2, H4, field }), field);
      }

      const bar = _decode_by_descending_pivots({
        target: S1, encode_fn: enc_bar, nparams: 15, field, what: 'barQ15 given (H2,H4)',
      });
      return [vals[0]].concat(q3, a47, q7, [vals[15]], bar);
    }

    return [31, build, extract];
  }

  if (m % 8 === 3) {
    const kk = Math.floor((m - 3) / 8);
    const inner_len = 2 * kk + 1;
    const [n_inner, build_inner, extract_inner] = _pair_free(inner_len, field);
    const s3_free = kk === 1 ? 1 : 2 * kk - 1;
    const s2_free = 4 * kk + 1;
    // [α0 | S3 free | inner | a | S2 free].
    const nvals = 1 + s3_free + n_inner + 1 + s2_free;

    function build(vals) {
      const alpha0 = vals[0];
      const S3 = vals.slice(1, 1 + s3_free).concat(kk === 1 ? [] : [one]);
      const [S1_1, S1_2] = build_inner(vals.slice(1 + s3_free, 1 + s3_free + n_inner));
      const a = vals[1 + s3_free + n_inner];
      const S2 = vals.slice(-s2_free).concat([one]);
      const T1 = add(sub(sq(S2), sq(S1_1)), S3);
      const T2 = addc(sub(sq(addc(S2, a)), sq(S1_2)), alpha0);
      return [T1, T2];
    }

    function extract(vals) {
      const alpha0 = vals[0];
      const inner = extract_inner(vals.slice(1 + s3_free, 1 + s3_free + n_inner));
      const a = vals[1 + s3_free + n_inner];
      const [, , Hs] = _poly_paper_splittable_pair({ n: inner_len, alpha: inner, field });
      const H2 = Hs[1];
      const S2poly = _poly_trim(vals.slice(-s2_free).concat([one]), field);
      const S2block = _solve_Q4kp1(S2poly, kk, H2, field);
      let S3block;
      if (kk === 1) {
        S3block = [vals[1]];
      } else {
        const S3poly = _poly_trim(vals.slice(1, 1 + s3_free).concat([one]), field);
        const Hs2 = _Q4kp1_powers(S2block, kk, H2, field);
        S3block = _solve_Qodd(S3poly, 2 * kk - 1, Hs2, field);
      }
      return [alpha0].concat(S3block, inner, [a], S2block);
    }

    return [nvals, build, extract];
  }

  if (m % 8 === 7) {
    const kk = Math.floor((m - 7) / 8);
    const inner_len = 2 * kk + 1;
    const [n_inner, build_inner, extract_inner] = _pair_free(inner_len, field);
    const s2_free = 2 * kk + 1;
    const s3_free = 4 * kk + 3;
    // [inner | a | S2 free | b | S3 free].
    const nvals = n_inner + 1 + s2_free + 1 + s3_free;

    function build(vals) {
      const [S1_1, S1_2] = build_inner(vals.slice(0, n_inner));
      const a = vals[n_inner];
      const S2 = vals.slice(n_inner + 1, n_inner + 1 + s2_free).concat([one]);
      const b = vals[n_inner + 1 + s2_free];
      const S3 = vals.slice(-s3_free).concat([one]);
      const T1 = add(sub(sq(S3), sq(S2)), S1_1);
      const T2 = add(sub(sq(addc(S3, b)), sq(addc(S2, a))), S1_2);
      return [T1, T2];
    }

    function extract(vals) {
      const inner = extract_inner(vals.slice(0, n_inner));
      const a = vals[n_inner];
      const S2poly = _poly_trim(vals.slice(n_inner + 1, n_inner + 1 + s2_free).concat([one]), field);
      const b = vals[n_inner + 1 + s2_free];
      const S3poly = _poly_trim(vals.slice(-s3_free).concat([one]), field);
      let [, , Hs] = _poly_paper_splittable_pair({ n: inner_len, alpha: inner, field });
      const [enc2, hs2] = _build_Q_encoder(2 * kk + 1, Hs, field);
      const S2block = _decode_by_descending_pivots({
        target: S2poly, encode_fn: enc2, nparams: 2 * kk + 1, field, what: 'Q_{2k+1}',
      });
      Hs = hs2(S2block);
      const [enc3] = _build_Q_encoder(4 * kk + 3, Hs, field);
      const S3block = _decode_by_descending_pivots({
        target: S3poly, encode_fn: enc3, nparams: 4 * kk + 3, field, what: 'Q_{4k+3}',
      });
      return inner.concat([a], S2block, [b], S3block);
    }

    return [nvals, build, extract];
  }

  throw new Error(`internal error: no pair parameterization for m=${m}`);
}

// py: tools/polychain.py:566
// Parameter block α' of the inner splittable pair for odd m from
// Ψ = x·T1(α')² + T2(α')² known in degrees >= m−1 (lem:compatible-power).
function _decode_pairsq(m, psi, field) {
  const n = m - 1;
  const [nvals, build, extract] = _pair_free(m, field);

  function enc(vals) {
    const [T1, T2] = build(vals);
    return _pairsq_psi(T1, T2, field);
  }

  // rows=range(n, 2*n+2) -> explicit array of row indices.
  const rows = [];
  for (let w = n; w < 2 * n + 2; w++) rows.push(w);

  const vals = _decode_by_descending_pivots({
    target: psi, encode_fn: enc, nparams: nvals, field, rows,
    what: `pair-squares (m=${m})`,
  });
  const alpha = extract(vals);

  const [T1, T2] = _poly_paper_splittable_pair({ n: m, alpha, field });
  const chk = _pairsq_psi(T1, T2, field);
  for (let w = n; w < 2 * n + 2; w++) {
    if (!field.eq(_poly_coeff(chk, w, field), _poly_coeff(psi, w, field))) {
      throw new Error(`pair-squares (m=${m}): decoded block failed verification at degree ${w}`);
    }
  }
  return alpha;
}

// ---------------------------------------------------------------------------
// The 8k+3 induction step (lem:8k+3-splittable)
// ---------------------------------------------------------------------------

// py: tools/polychain.py:598
// Decode P_{8k+3} = x·S_2² + (S_2+a)² − x·S1_1² − S1_2² + x·S_3 + α_0
// following the proof of `lem:8k+3-splittable`:
//
//   1. square gadget at degree 4k+1 recovers (S_2, a); boundary error −1;
//   2. the window ≥ 2k of Ψ = x·S1_1² + S1_2² recovers the inner
//      splittable-pair block for 2k+1 (descending pivots — the numerical
//      realization of the compatibility/square-closure certificate);
//   3. the residual x·S_3 + α_0 gives α_0 and the S_3 = Q_{2k-1} block;
//   4. S_2 = Q_{4k+1}(x, H_2) is decoded given the recovered H_2.
function _decode_pair_8k3(coeffs, field) {
  const n = _poly_degree(coeffs);
  const k = Math.floor((n - 3) / 8);
  const m = 2 * k + 1;
  const one = field.one();
  const x = _x(field);

  // 1. Outer square gadget; the error term −x·S1_1² contributes −1 at degree 4k+1.
  const [S2poly, a] = _decode_square_gadget({
    G: coeffs, field, boundary_error_coeff_deg_d: field.neg(one),
  });
  const P1 = _poly_sub(coeffs, _square_gadget_poly(S2poly, a, field), field);

  // 2. Ψ = x·S1_1² + S1_2² on the window ≥ 2k (boundary at 2k corrected by
  //    the known top coefficient of x·S_3: 1 for k>1, 0 for k=1).
  const psi = [];
  for (let i = 0; i < 2 * m; i++) psi.push(field.zero());
  for (let d = 2 * k + 1; d < 4 * k + 2; d++) {
    psi[d] = field.neg(_poly_coeff(P1, d, field));
  }
  const s3_top = k > 1 ? one : field.zero();
  psi[2 * k] = field.sub(s3_top, _poly_coeff(P1, 2 * k, field));

  const inner = _decode_pairsq(m, psi, field);
  const [T1i, T2i, Hs] = _poly_paper_splittable_pair({ n: m, alpha: inner, field });
  const H2 = Hs[1];

  // 3. Residual x·S_3 + α_0.
  const psi_full = _poly_add(
    _poly_shift_xk(_poly_square(T1i, field), 1, field),
    _poly_square(T2i, field),
    field
  );
  const low = _poly_add(P1, psi_full, field);
  const alpha0 = _poly_coeff(low, 0, field);
  const S3poly = _shift_down(low, field);

  // 4. Sub-gadget parameter blocks.
  function enc_S2(av) {
    const [q] = _poly_paper_Q_2lp1k_minus_1_with_powers({
      k, l: 1, alpha: av.slice(), Hs: [x, H2], field,
    });
    return _poly_trim(q, field);
  }

  const S2block = _decode_by_descending_pivots({
    target: S2poly, encode_fn: enc_S2, nparams: 4 * k + 1, field, what: 'Q_{4k+1} given H2',
  });

  let S3block;
  if (k === 1) {
    if (_poly_degree(S3poly) > 0) {
      throw new Error('8k+3 decode: expected scalar S_3 for k=1');
    }
    S3block = [_poly_coeff(S3poly, 0, field)];
  } else {
    const [, hs2_raw] = _poly_paper_Q_2lp1k_minus_1_with_powers({
      k, l: 1, alpha: S2block, Hs: [x, H2], field,
    });
    const Hs2 = [x, H2].concat(hs2_raw.slice(2));

    function enc_S3(av) {
      const [q] = _poly_paper_Q_for_odd_degree_with_powers({
        deg: 2 * k - 1, alpha: av.slice(), Hs: Hs2, field,
      });
      return _poly_trim(q, field);
    }

    S3block = _decode_by_descending_pivots({
      target: S3poly, encode_fn: enc_S3, nparams: 2 * k - 1, field, what: 'Q_{2k-1}',
    });
  }

  const alpha = [alpha0].concat(S3block, inner, [a], S2block);
  if (alpha.length !== n) {
    throw new Error('internal error: 8k+3 parameter count mismatch');
  }
  return alpha;
}

// ---------------------------------------------------------------------------
// The 8k+7 induction step (lem:8k+7-splittable)
// ---------------------------------------------------------------------------

// py: tools/polychain.py:687
// Decode P_{8k+7} = x·S_3² + (S_3+b)² − x·S_2² − (S_2+a)² + P_{2k+1}
// following the proof of `lem:8k+7-splittable`: two nested square gadgets,
// then recursion on P_{2k+1}, then the Q blocks for S_2 and S_3.
function _decode_pair_8k7(coeffs, field) {
  const n = _poly_degree(coeffs);
  const k = Math.floor((n - 7) / 8);
  if (k < 2) {
    throw new Error('internal error: 8k+7 decoding requires k >= 2 (15 is special-cased)');
  }
  const one = field.one();

  const [S3poly, b] = _decode_square_gadget({
    G: coeffs, field, boundary_error_coeff_deg_d: field.neg(one),
  });
  const P1 = _poly_sub(coeffs, _square_gadget_poly(S3poly, b, field), field);

  const G2 = _poly_scale_int(P1, -1, field); // = x·S_2² + (S_2+a)² − P_{2k+1}
  const [S2poly, a] = _decode_square_gadget({
    G: G2, field, boundary_error_coeff_deg_d: field.neg(one),
  });
  const Pm = _poly_add(P1, _square_gadget_poly(S2poly, a, field), field); // = P_{2k+1}

  const inner = _decode_odd(_poly_trim(Pm, field), field, { pair_context: true });
  let [, , Hs] = _poly_paper_splittable_pair({ n: 2 * k + 1, alpha: inner, field });

  const [enc2, hs2] = _build_Q_encoder(2 * k + 1, Hs, field);
  const S2block = _decode_by_descending_pivots({
    target: S2poly, encode_fn: enc2, nparams: 2 * k + 1, field, what: 'Q_{2k+1}',
  });
  Hs = hs2(S2block);

  const [enc3] = _build_Q_encoder(4 * k + 3, Hs, field);
  const S3block = _decode_by_descending_pivots({
    target: S3poly, encode_fn: enc3, nparams: 4 * k + 3, field, what: 'Q_{4k+3}',
  });

  const alpha = inner.concat([a], S2block, [b], S3block);
  if (alpha.length !== n) {
    throw new Error('internal error: 8k+7 parameter count mismatch');
  }
  return alpha;
}

// ---------------------------------------------------------------------------
// Special case 27
// ---------------------------------------------------------------------------

// py: tools/polychain.py:736
// Decode the special-case construction for 27:
//   P = (x+1)·T_1 + S_3² − H_2² + α_0,   T_1 = S_1² − S_2² + α_1,
//   S_1 = Q_13(x,H_2)  (which yields H_4),  S_2 = Q_3(x,H_2),
//   S_3 = Q_7(x,H_2,H_4).
function _decode_pair_27(coeffs, field) {
  const one = field.one();
  const x = _x(field);
  const x_plus_1 = [one, one];

  // T_1 top coefficients by back-substitution on (x+1)T_1 (rows >= 15 clean;
  // row 14 carries the +1 of the monic S_3²).
  const t = new Map([[26, one]]);
  for (let j = 26; j > 14; j--) {
    t.set(j - 1, field.sub(_poly_coeff(coeffs, j, field), t.get(j)));
  }
  t.set(13, field.sub(field.sub(_poly_coeff(coeffs, 14, field), t.get(14)), one));

  // S_1² agrees with T_1 in degrees >= 13; monic square root (lem:monic-from-power, m=2).
  const S1_sq = [];
  for (let i = 0; i < 27; i++) S1_sq.push(field.zero());
  for (let j = 13; j < 27; j++) {
    S1_sq[j] = t.get(j);
  }
  const S1 = _monic_sqrt_from_high_square_coeffs(_poly_trim(S1_sq, field), 13, field);

  const P2 = _poly_sub(coeffs, _poly_mul(x_plus_1, _poly_square(S1, field), field), field);

  // S_3² from rows 8..14 of P2 (+1 correction at row 7 from the monic Q_3²).
  const S3_sq = [];
  for (let i = 0; i < 15; i++) S3_sq.push(field.zero());
  for (let j = 8; j < 15; j++) {
    S3_sq[j] = _poly_coeff(P2, j, field);
  }
  S3_sq[7] = field.add(_poly_coeff(P2, 7, field), one);
  const S3 = _monic_sqrt_from_high_square_coeffs(_poly_trim(S3_sq, field), 7, field);

  const P3 = _poly_sub(P2, _poly_square(S3, field), field);

  // Remaining low block: P3 = −(x+1)·Q_3² + (x+1)·α_1 − H_2² + α_0, read
  // from degree 6 downwards in the coefficients of Q_3 = x³+γ₂x²+γ₁x+γ₀
  // and H_2 = x²+bx+c (a triangular chain, one new quantity per degree).
  const low = _decode_27_low_block(P3, field);
  const H2 = [low[2], low[3], one];

  // S_1 = Q_13(x, H_2): the k=3, l=1 known-powers gadget; byproduct H_4.
  function enc_q13(a) {
    const [q] = _poly_paper_Q_2lp1k_minus_1_with_powers({
      k: 3, l: 1, alpha: a.slice(), Hs: [x, H2], field,
    });
    return _poly_trim(q, field);
  }

  const q13 = _decode_by_descending_pivots({
    target: S1, encode_fn: enc_q13, nparams: 13, field, what: 'Q13 given H2',
  });
  const [, hs_raw] = _poly_paper_Q_2lp1k_minus_1_with_powers({
    k: 3, l: 1, alpha: q13, Hs: [x, H2], field,
  });
  const H4 = hs_raw[2];

  const q7 = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
    Q: S3, k: 3, Hs: [_x(field), H2, H4], field,
  });

  const alpha = low.concat(q7, q13);
  if (alpha.length !== 27) {
    throw new Error('internal error: 27 parameter count mismatch');
  }
  return alpha;
}

// ---------------------------------------------------------------------------
// Special case 31
// ---------------------------------------------------------------------------

// py: tools/polychain.py:806
// Decode the special-case construction for 31:
//   P = x·S_1² + (S_1+α_15)² − x·S_2² − H_4² + x·S_3 + α_0,
//   S_1 = bar-Q_15(x,H_2,H_4), S_2 = Q_7(x,H_2,H_4), S_3 = Q_3(x,H_2),
//   H_4 = H_2² − (x+α_5)² + α_4.
function _decode_pair_31(coeffs, field) {
  const one = field.one();

  const [S1, a15] = _decode_square_gadget({
    G: coeffs, field, boundary_error_coeff_deg_d: field.neg(one),
  });
  const P1 = _poly_sub(coeffs, _square_gadget_poly(S1, a15, field), field);

  // S_2² from −P1 on rows 9..15 (row 8 corrected by the monic H_4²).
  const S2_sq = [];
  for (let i = 0; i < 15; i++) S2_sq.push(field.zero());
  for (let d = 9; d < 16; d++) {
    S2_sq[d - 1] = field.neg(_poly_coeff(P1, d, field));
  }
  S2_sq[7] = field.neg(field.add(_poly_coeff(P1, 8, field), one));
  const S2 = _monic_sqrt_from_high_square_coeffs(_poly_trim(S2_sq, field), 7, field);

  const P2 = _poly_add(P1, _poly_shift_xk(_poly_square(S2, field), 1, field), field);

  // H_4² from −P2 on rows 5..8 (row 4 corrected by the monic x·S_3).
  const H4_sq = [];
  for (let i = 0; i < 9; i++) H4_sq.push(field.zero());
  for (let d = 5; d < 9; d++) {
    H4_sq[d] = field.neg(_poly_coeff(P2, d, field));
  }
  H4_sq[4] = field.sub(one, _poly_coeff(P2, 4, field));
  const H4 = _monic_sqrt_from_high_square_coeffs(_poly_trim(H4_sq, field), 4, field);

  const low = _poly_add(P2, _poly_square(H4, field), field); // = x·S_3 + α_0
  const alpha0 = _poly_coeff(low, 0, field);
  const S3 = _shift_down(low, field);

  // α_4..α_7 from H_4 = H_2² − (x+α_5)² + α_4 with H_2 = x² + α_7 x + α_6.
  function enc_H4(a) {
    const H2 = [a[2], a[3], one];
    return _poly_add_const(
      _poly_sub(_poly_square(H2, field), _poly_square([a[1], one], field), field),
      a[0],
      field
    );
  }

  const a47 = _decode_by_descending_pivots({
    target: H4, encode_fn: enc_H4, nparams: 4, field, what: 'H4 block',
  });
  const H2 = [a47[2], a47[3], one];

  const q3 = _decode_Q3_coeffs_to_alpha_given_H2(S3, H2, field);
  const q7 = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
    Q: S2, k: 3, Hs: [_x(field), H2, H4], field,
  });

  function enc_bar(a) {
    return _poly_trim(_poly_paper_barQ_15({ alpha: a.slice(), H2, H4, field }), field);
  }

  const bar = _decode_by_descending_pivots({
    target: S1, encode_fn: enc_bar, nparams: 15, field, what: 'barQ15 given (H2,H4)',
  });

  const alpha = [alpha0].concat(q3, a47, q7, [a15], bar);
  if (alpha.length !== 31) {
    throw new Error('internal error: 31 parameter count mismatch');
  }
  return alpha;
}

// py: tools/polychain.py:1170
// Run a callable with the peeled known-powers gadget mode enabled.
function _with_peeled(thunk) {
  set_peeled_q(true);
  try {
    return thunk();
  } finally {
    set_peeled_q(false);
  }
}

// =====================================================================
// Exports
// =====================================================================
export {
  Rat,
  Field,
  AffineForm,
  MulGate,
  PolynomialChain,
  ChainBuilder,
  GF,
  rationals,
  default_field,
  encode,
  decode,
  compile_paper_params_chain,
  set_peeled_q,
  makeRng,
  _poly_trim,
  _poly_degree,
  _poly_coeff,
  _poly_eq,
  _poly_paper_P_from_params,
};
