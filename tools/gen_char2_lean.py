#!/usr/bin/env python3
"""Emit kernel-checked Lean certificates for the website's fixed char-2 circuits.

No circuit or pivot search is performed. We replay the existing, explicitly
specified coordinate changes in GF(2)[q][x], with unrestricted exponents, then
emit ordinary ring-identity proofs and causal-tail certificates for Lean.
Python's checks are diagnostics: Lean must independently check every identity.
Output is JSON {path, content}, or --stats for a compact symbolic audit.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.char2_polynomial import F2Poly, XPoly, X, ZERO, ONE, _NAMES


def specs():
    command = "import {CIRCUITS} from './website/js/char2.js'; console.log(JSON.stringify(CIRCUITS));"
    return json.loads(subprocess.check_output(
        ["node", "--input-type=module", "-e", command], cwd=ROOT, text=True))


def circuit(spec, a):
    wires = {"x": X}
    def factor(f):
        out = sum((wires[t] for t in f["t"]), XPoly([]))
        return out if f["k"] is None else out + a[f["k"]]
    for gate in spec["gates"]:
        wires[gate["w"]] = factor(gate["l"]) * factor(gate["r"])
    return wires, factor(spec["out"])


def array_expression(source, start):
    pos = source.index("[", start)
    depth = 0
    for i in range(pos, len(source)):
        if source[i] == "[": depth += 1
        if source[i] == "]": depth -= 1
        if depth == 0:
            return source[pos:i + 1]
    raise ValueError("unterminated coordinate array")


def offsets(n, spec, q):
    """Transcribe the named certificate, never rediscover its pivots."""
    js = (ROOT / "website/js/char2.js").read_text()
    js = js[js.index("const KEYS_FROM_Q = {"):]
    js = re.sub(r"//[^\n]*", "", js)
    env = {"Q": q, "M": lambda a, b: a * b, "F": type("Ops", (), {"mul": staticmethod(lambda a, b: a*b)})}
    if n in (3, 5, 7, 9, 15, 19, 21):
        start = js.index(f"{n}: (Q, F) =>")
        return eval(array_expression(js, start), {"__builtins__": {}}, env)
    if n == 11:
        start = js.index("return [", js.index("11: (Q, F) =>"))
        for i in range(n):
            env[f"q{i}"] = q[i]
            for e in range(2, 7): env[f"q{i}_{e}"] = q[i] ** e
        return eval(array_expression(js, start), {"__builtins__": {}}, env)
    if n == 13:
        # decode_n13.py, in its explicit recovery order. The only coordinate
        # blocks are q1=a11+a12 and q9=a3+a4, each with the displayed inverse.
        return [q[12], q[6], q[11], q[8], q[9]+q[8], q[0], q[10],
                q[7], q[4], q[3], q[5], q[1]+q[2], q[2]]
    if n == 17:
        from char2.verify_n17_uniform_symbolic import _build_from_triangular_coordinates
        _, names, a = _build_from_triangular_coordinates()
        index = dict(zip(names, q))
        def convert(expr):
            acc = ZERO
            for monomial in expr.monos:
                term = ONE
                for name in monomial: term *= index[name]
                acc += term
            return acc
        return [convert(a[f"a{i}"]) for i in range(n)]
    if n == 23:
        # The explicit key inverse from verify_n23_unitriangular_symbolic.py,
        # with its terminal block changed to the website's two unit pivots.
        q = list(q)
        q[18], q[19] = q[19], q[18] + (q[0]+q[8]+1)*q[19]
        a = [ZERO] * 23
        a[0], a[1], a[2] = q[2], q[1]+q[2], q[0]
        a[3], a[4], a[5] = q[3]+q[5]+q[6], q[4]+q[5]+q[6]+q[7], q[16]
        a[6], a[7] = q[8], q[11]+q[7]*q[16]+q[16]**2+q[20]
        a[12], a[13], a[14] = q[15]+q[16], q[17]+q[18], q[7]+q[16]
        a[15], a[16], a[17], a[18] = q[20], q[18], q[21], q[5]
        a[20], a[21] = q[6], q[19]
        rho = q[0]*q[7]*q[16]+q[0]*q[16]**2+q[0]*q[20]+q[7]*q[8]*q[16]+q[7]*q[16]+q[8]*q[16]**2+q[8]*q[20]+q[16]**2
        aa = q[0]+q[3]+q[5]+q[6]+q[7]**2+q[8]+q[9]+q[11]+1
        bb = q[0]*q[7]+q[3]*q[7]+q[5]*q[7]+q[6]*q[7]+q[7]*q[8]+q[7]*q[9]+q[7]*q[11]+q[7]+1
        cc = q[0]+q[3]+q[5]+q[6]+q[8]+q[9]+q[11]+1
        a[11] = q[13]+q[16]**4+aa*q[16]**2+bb*q[16]+q[20]**2+cc*q[20]+q[18]+q[21]
        a[10] = q[12]+rho+q[16]+a[11]+a[12]
        a[9] = q[10]+rho+a[11]+q[20]+q[18]
        a[8] = q[9]+q[16]**2+q[7]*q[16]+a[10]+q[20]+q[18]
        _, baseline = circuit(spec, a)
        a[19], a[22] = q[14]+baseline.coeff(8), q[22]
        return a
    if n == 25:
        # The published 24 elementary coordinate substitutions. Each tail
        # is read from its specified row and its specified unit pivot.
        order = [2,0,1,3,4,12,6,5,23,7,9,13,8,17,10,11,15,19,21,22,18,16,14,20]
        active = [F2Poly.var(f"b{i}") for i in range(24)]
        a = active + [q[24]]
        remaining = set(range(24))
        for i, pivot in enumerate(order):
            _, p = circuit(spec, a)
            coeff = p.coeff(24-i)
            baseline = coeff.subs_many({f"b{j}": ZERO for j in remaining})
            residual = coeff + baseline
            assert residual.degree(f"b{pivot}") == 1
            assert residual.coeff_wrt(f"b{pivot}", 1) == ONE
            tail = residual + active[pivot]
            assert f"b{pivot}" not in tail.variables()
            a = [expr.subs(f"b{pivot}", q[i]+tail) for expr in a]
            remaining.remove(pivot)
        return a
    raise ValueError(n)


def form(p):
    # Deterministic sparse Horner grouping avoids enormous elaboration terms.
    # This only formats the checked certificate; it is not a decoder search.
    if len(p.t) > 24:
        v = min(v for m in p.t for v, _ in m)
        groups = {}
        for m in p.t:
            e = dict(m).get(v, 0)
            groups.setdefault(e, set()).add(tuple((w, k) for w, k in m if w != v))
        terms = []
        for e, ms in sorted(groups.items()):
            c = F2Poly(ms)
            power = f"q {int(_NAMES[v][1:])}"
            if e != 1: power = f"({power}) ^ {e}"
            term = form(c)
            terms.append(term if e == 0 else power if c == ONE else f"({term}) * {power}")
        return " + ".join(f"({t})" for t in terms)
    terms = []
    for m in sorted(p.t, key=lambda m: (sum(e for _, e in m), m)):
        factors = []
        for v, e in m:
            name = _NAMES[v]
            assert name.startswith("q"), name
            f = f"q {int(name[1:])}"
            factors.append(f if e == 1 else f"({f}) ^ {e}")
        terms.append(" * ".join(factors) or "1")
    def balanced(parts):
        if len(parts) <= 24: return " + ".join(parts) or "0"
        mid = len(parts)//2
        return "(" + balanced(parts[:mid]) + ") +\n      (" + balanced(parts[mid:]) + ")"
    return balanced(terms)


def poly_form(p, coefficient=None):
    terms = []
    for d in range(p.degree + 1):
        c = p.coeff(d)
        if not c: continue
        scalar = f"C ({coefficient(d) if coefficient and c != ONE else form(c)})"
        power = f"X ^ {d}"
        terms.append(scalar if d == 0 else power if c == ONE else f"{scalar} * {power}")
    return " +\n    ".join(terms) or "0"


def factor_source(f, wires, key):
    parts = [wires[t] for t in f["t"]]
    if f["k"] is not None: parts.append(key(f["k"]))
    return " + ".join(parts) or "0"


def raw_circuit(spec):
    """Existing Cost.Circuit syntax: shared binds, affine factors, paid products."""
    names = [g["w"] for g in spec["gates"]]
    def label(name, depth):
        if isinstance(name, int): out, level = str(name+1), 0
        elif name == "x": out, level = "0", 0
        else: level = names.index(name)+1; out = "Sum.inr 0"
        for _ in range(depth-level): out = f"Sum.inl ({out})"
        return f"(.input ({out}))"
    def add(parts):
        ans = parts[0]
        for p in parts[1:]: ans = f"(.add {ans} {p})"
        return ans
    def factor(f, depth):
        p = [label(t, depth) for t in f["t"]]
        if f["k"] is not None: p.append(label(f["k"], depth))
        return add(p)
    lines = []
    for i, gate in enumerate(spec["gates"]):
        lines.append(f"  .bind (.mul {factor(gate['l'], i)} {factor(gate['r'], i)}) (")
    lines.append("  " + factor(spec["out"], len(names)) + ")"*len(names))
    return "\n".join(lines)


def bound_sum(parts):
    proof = parts[0]
    for p in parts[1:]:
        proof = f"(natDegree_add_le_of_degree_le {proof} {p})"
    return proof


def monomial_bound(c, d):
    if d == 0: return "(by simp only [natDegree_C]; omega)"
    if c == ONE:
        return "(le_trans (natDegree_X_pow_le _) (by omega))"
    return "(le_trans (natDegree_C_mul_X_pow_le _ _) (by omega))"


def polynomial_bound(p):
    return bound_sum([monomial_bound(p.coeff(d), d) for d in range(p.degree+1) if p.coeff(d)])


def factor_bound(f):
    parts = ["(by simp only [natDegree_X]; omega)" if t == "x" else
             f"(le_trans (normal_{t}_degree q) (by omega))" for t in f["t"]]
    if f["k"] is not None: parts.append("(by simp only [natDegree_C]; omega)")
    return bound_sum(parts)


def certificate_data(n):
    spec = specs()[str(n)]
    q = [F2Poly.var(f"q{i}") for i in range(n)]
    a = offsets(n, spec, q)
    wires, p = circuit(spec, a)
    rows = list(reversed(range(n)))
    depths = [0]*n
    if n == 7: depths = spec["rootDepths"]
    if n == 13: rows = [12,11,10,7,6,9,8,5,4,3,1,2,0]
    if n == 17:
        rows = [16,15,13,14,12,11,10,9,8,7,6,5,4,3,2,1,0]
        depths = [0,0,1,0,0,0,0,1,2,0,0,0,0,0,0,0,0]
    assert p.degree == n and p.coeff(n) == ONE
    tails = [p.coeff(row) + q[i]**(2**depths[i]) for i, row in enumerate(rows)]
    for i, tail in enumerate(tails):
        assert all(int(v[1:]) < i for v in tail.variables()), (n, i, tail.variables())
    return spec, a, wires, p, rows, depths, tails


def generate(n, data):
    spec, a, wires, p, rows, depths, tails = data
    frob = any(depths)
    out = ["import FastPoly.Examples.Char2Triangular",
           "import FastPoly.Examples.Char2Coefficients",
           "import FastPoly.Examples.Char2Ring", "import FastPoly.Cost.MultiplicationProgram",
           "import Mathlib.Tactic.IntervalCases", "import Mathlib.Tactic.FinCases",
           *( ["import FastPoly.Examples.Char2Frobenius"] if frob else []), "",
           "/-! Generated by tools/gen_char2_lean.py. Every identity is checked by Lean.",
           f"The website's degree-{n} circuit, with explicit normalized coordinates.",
           "Preprocessing is outside the online multiplication count. -/", "",
           f"namespace FastPoly.Char2Degree{n}", "open Polynomial Char2Certificate", "",
           "set_option maxRecDepth 8192", "set_option maxHeartbeats 1000000",
           "set_option linter.unusedSimpArgs false", "set_option linter.unusedVariables false",
           "set_option linter.unusedSectionVars false",
           "set_option linter.unusedTactic false", "set_option linter.unreachableTactic false", "",
           "variable {F : Type*} [Field F] [CharP F 2]" + (" [PerfectRing F 2]" if frob else ""), "",
           "/-- Literal fixed shared circuit; its count is computed from syntax. -/",
           "def circuit : Cost.Circuit F ℕ 1 :=", raw_circuit(spec), "",
           f"theorem multiplication_count : (circuit (F := F)).gates.multiplications = {len(spec['gates'])} := rfl", "",
           "def program : Cost.MultiplicationProgram F ℕ 1 " + str(len(spec['gates'])) + " :=",
           "  ⟨circuit, multiplication_count⟩", ""]
    out += [f"def offset_{i} (q : ℕ → F) : F := {form(c)}\n" for i, c in enumerate(a)]
    out += ["def offsets (q : ℕ → F) : ℕ → F"]
    out += [f"  | {i} => offset_{i} q" for i in range(n)] + [f"  | _ + {n} => 0", ""]
    wnames = {"x": "X"}
    normnames = {"x": "X"}
    for gate in spec["gates"]:
        name = "wire_" + gate["w"]
        norm = "normal_" + gate["w"]
        row = "row_" + gate["w"]
        row_defs = [f"{row}_{d}" for d in range(wires[gate['w']].degree+1)
                    if wires[gate['w']].coeff(d) not in (ZERO, ONE)]
        out += [f"def {row}_{d} (q : ℕ → F) : F := {form(wires[gate['w']].coeff(d))}\n"
                for d in range(wires[gate['w']].degree+1)
                if wires[gate['w']].coeff(d) not in (ZERO, ONE)]
        left = factor_source(gate["l"], wnames, lambda i: f"C (a {i})")
        right = factor_source(gate["r"], wnames, lambda i: f"C (a {i})")
        out += [f"noncomputable def {name} (a : ℕ → F) : F[X] := ({left}) * ({right})", "",
                f"noncomputable def {norm} (q : ℕ → F) : F[X] :=", "  " + poly_form(wires[gate["w"]], lambda d: f"{row}_{d} q"), "",
                f"theorem {norm}_degree (q : ℕ → F) : ({norm} q).natDegree ≤ {wires[gate['w']].degree} := by",
                f"  unfold {norm}", "  exact " + polynomial_bound(wires[gate["w"]]), ""]
        prev = list(dict.fromkeys(gate["l"]["t"] + gate["r"]["t"]))
        rewrites = [name] + [f"wire_{t}_offsets" for t in prev if t != "x"]
        norms = [norm] + [f"normal_{t}" for t in prev if t != "x"]
        row_defs += [f"row_{t}_{d}" for t in prev if t != "x"
                     for d in range(wires[t].degree+1) if wires[t].coeff(d) not in (ZERO, ONE)]
        row_defs += [f"offset_{i}" for i in dict.fromkeys([gate['l']['k'], gate['r']['k']]) if i is not None]
        dl = max(wires[t].degree for t in gate["l"]["t"])
        dr = max(wires[t].degree for t in gate["r"]["t"])
        assert dl+dr == wires[gate["w"]].degree
        coeff_proof = ["rw [coeff_mul] <;>",
                "  (try simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,",
                "    Finset.sum_range_succ, Finset.sum_range_zero]) <;>",
                "  norm_num only [" + ", ".join(norms) + ",",
                "    coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_X, coeff_C,",
                "    ite_true, ite_false, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>",
                "  (try simp only [offsets" + "".join(", " + r for r in row_defs) + "]) <;>",
                "  ring_char2"]
        if n >= 17:
            nl = factor_source(gate['l'], normnames, lambda i: f"C (offsets q {i})")
            nr = factor_source(gate['r'], normnames, lambda i: f"C (offsets q {i})")
            for k in range(dl+dr+1):
                out += [f"theorem {name}_coeff_{k} (q : ℕ → F) :",
                        f"    (({nl}) * ({nr})).coeff {k} = ({norm} q).coeff {k} := by"]
                out += ["  " + line for line in coeff_proof] + [""]
        out += [f"theorem {name}_offsets (q : ℕ → F) : {name} (offsets q) = {norm} q := by",
                "  rw [" + ", ".join(rewrites) + "]",
                f"  apply bounded_ext (d := {dl+dr})",
                "  · exact le_trans natDegree_mul_le (Nat.add_le_add",
                f"      (show _ ≤ {dl} from {factor_bound(gate['l'])})",
                f"      (show _ ≤ {dr} from {factor_bound(gate['r'])}))",
                f"  · exact {norm}_degree q", "  · intro k hk"]
        if n >= 17:
            out += ["    interval_cases k"]
            out += [f"    · exact {name}_coeff_{k} q" for k in range(dl+dr+1)]
        else:
            out += ["    interval_cases k <;>"] + ["      " + line for line in coeff_proof]
        out += [""]
        wnames[gate["w"]] = f"{name} a"
        normnames[gate["w"]] = f"{norm} q"
    output = factor_source(spec["out"], wnames, lambda i: f"C (a {i})")
    out += ["noncomputable def polynomial (a : ℕ → F) : F[X] := " + output, "",
            "theorem program_eval (a : ℕ → F) :",
            "    (program (F := F)).circuit.eval (fun i => if i = 0 then X else C (a (i-1))) 0 = polynomial a := rfl", ""]
    out += [f"def tail_{i} (q : ℕ → F) : F := {form(t)}\n" for i, t in enumerate(tails)]
    out += ["def tail (i : ℕ) (q : ℕ → F) : F :=", "  match i with"]
    out += [f"  | {i} => tail_{i} q" for i in range(n)] + [f"  | _ + {n} => 0", "",
            f"theorem tail_causal : Causal {n} (tail (F := F)) := by", "  intro i hi q r h", "  interval_cases i"]
    for i, t in enumerate(tails):
        deps = sorted(int(v[1:]) for v in t.variables())
        args = ["tail", f"tail_{i}"] + [f"h {j} (by omega)" for j in deps]
        out += ["  · simp only [" + ", ".join(args) + "]"]
    out += ["", "noncomputable def pivot (i : ℕ) : F ≃ F :=", "  match i with"]
    out += [f"  | {i} => frobeniusPivot {d}" for i,d in enumerate(depths) if d]
    out += ["  | _ => Equiv.refl F", ""]
    explicit_sum = "0" + "".join(
        f" + C (pivot {rows.index(j)} (extendFin q {rows.index(j)}) + tail {rows.index(j)} (extendFin q)) * X ^ {j}"
        for j in range(n))
    rhs_bound = bound_sum(["(le_trans (natDegree_X_pow_le _) (by omega))",
        bound_sum(["(by simp only [natDegree_zero]; omega)"] +
            ["(le_trans (natDegree_C_mul_X_pow_le _ _) (by omega))"]*n)])
    out += ["", f"def rows : Fin {n} ≃ Fin {n} where",
            "  toFun := ![" + ", ".join(map(str, rows)) + "]",
            "  invFun := ![" + ", ".join(str(rows.index(i)) for i in range(n)) + "]",
            "  left_inv i := by fin_cases i <;> rfl", "  right_inv i := by fin_cases i <;> rfl", "",
            f"noncomputable def coefficients : (Fin {n} → F) ≃ (Fin {n} → F) :=",
            "  coefficientEquiv pivot tail tail_causal rows", "",
            f"noncomputable def family (q : Fin {n} → F) : F[X] := polynomial (offsets (extendFin q))", "",
            f"theorem family_normal (q : Fin {n} → F) :",
            "    family q = monicOfCoefficients (coefficients q) := by",
            "  rw [family, polynomial" + "".join(f", wire_{t}_offsets" for t in spec["out"]["t"]) + "]",
            "  simp only [monicOfCoefficients, Finset.sum_range_succ, Finset.sum_range_zero]",
            f"  change _ = X ^ {n} + ({explicit_sum})",
            f"  apply bounded_ext (d := {n})",
            "  · exact " + factor_bound(spec["out"]).replace("_degree q", "_degree (extendFin q)"),
            "  · exact " + rhs_bound,
            "  · intro k hk", "    interval_cases k <;>",
            "      norm_num only [" + ", ".join(f"normal_{t}" for t in spec["out"]["t"]) + ",",
            "        coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C, coeff_zero,",
            "        ite_true, ite_false, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>",
            "      (try simp only [offsets, " +
            (f"offset_{spec['out']['k']}, " if spec['out']['k'] is not None else "") +
            "tail, " + ", ".join(f"tail_{i}" for i in range(n)) + ", pivot, Equiv.refl_apply, " +
            ("frobeniusPivot_apply, Nat.reducePow, " if frob else "") +
            ", ".join(f"row_{t}_{d}" for t in spec["out"]["t"]
                for d in range(wires[t].degree+1) if wires[t].coeff(d) not in (ZERO, ONE)) + "]) <;>",
            "      ring_char2", "",
            f"theorem evaluation_bijective (x : Fin {n} → F) (hx : Function.Injective x) :",
            "    Function.Bijective (fun q => fun i => (family q).eval (x i)) :=",
            "  Char2Certificate.evaluation_bijective (by omega) _ tail tail_causal rows family family_normal x hx", "",
            "/-- Preprocessed gate offsets for any requested monic polynomial. -/",
            f"noncomputable def decode (c : Fin {n} → F) : ℕ → F := offsets (extendFin (coefficients.symm c))", "",
            f"theorem decode_correct (c : Fin {n} → F) :",
            "    polynomial (decode c) = monicOfCoefficients c := by",
            "  have h := family_normal (coefficients.symm c)",
            "  simpa only [family, decode, Equiv.apply_symm_apply] using h", "",
            "/-- The same literal counted circuit realizes every prescribed coefficient vector. -/",
            f"theorem program_decode_correct (c : Fin {n} → F) :",
            "    (program (F := F)).circuit.eval",
            "      (fun i => if i = 0 then X else C (decode c (i-1))) 0 = monicOfCoefficients c :=",
            "  (program_eval (decode c)).trans (decode_correct c)", "",
            f"end FastPoly.Char2Degree{n}", ""]
    return "\n".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", type=int, choices=list(range(3, 26, 2)))
    parser.add_argument("--stats", action="store_true")
    parser.add_argument("--apply", action="store_true", help="install generated source using apply_patch")
    parser.add_argument("--check", action="store_true", help="check the source matches the current website certificate")
    args = parser.parse_args()
    data = certificate_data(args.degree)
    spec, a, wires, p, rows, depths, tails = data
    if args.stats:
        print(json.dumps({"degree": args.degree, "multiplications": len(spec["gates"]),
            "max_offset_terms": max(len(c.t) for c in a),
            "wire_terms": {k: sum(len(v.coeff(j).t) for j in range(v.degree+1)) for k,v in wires.items()},
            "tail_terms": [len(t.t) for t in tails], "rows": rows, "root_depths": depths}))
    else:
        path = f"FastPoly/Examples/Char2Degree{args.degree}.lean"
        content = generate(args.degree, data)
        if args.check:
            target = ROOT / path
            if not target.exists() or target.read_text() != content:
                raise SystemExit(f"Certificate source differs: {path}; regenerate with --apply")
            print(f"Certificate source matches: {path}")
        elif args.apply:
            target = ROOT / path
            if target.exists():
                old = target.read_text()
                if old == content:
                    print(f"Unchanged: {path}")
                    return
                assert "Generated by tools/gen_char2_lean.py" in old
                patch = f"*** Begin Patch\n*** Update File: {path}\n@@\n"
                patch += "\n".join("-"+line for line in old.splitlines()) + "\n"
                patch += "\n".join("+"+line for line in content.splitlines()) + "\n*** End Patch\n"
            else:
                patch = f"*** Begin Patch\n*** Add File: {path}\n"
                patch += "\n".join("+"+line for line in content.splitlines()) + "\n*** End Patch\n"
            subprocess.run(["apply_patch"], input=patch, text=True, check=True, cwd=ROOT)
        else:
            print(json.dumps({"path": path, "content": content}))


if __name__ == "__main__":
    main()
