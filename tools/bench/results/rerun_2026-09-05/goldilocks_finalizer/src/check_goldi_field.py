# Verifies test_goldi_field output against Python big-int arithmetic mod p.
import sys
P = 2**64 - 2**32 + 1
n = 0; bad = 0; nf = 0
for line in sys.stdin:
    f = line.split()
    if f[0] == 'F':
        k = [int(t, 16) for t in f[1:6]]; x = int(f[6], 16); g4 = int(f[7], 16); g5 = int(f[8], 16)
        assert all(v < P for v in k) and x < P
        y = (x * (x + k[0]) + k[1]) % P
        e4 = (y * (y + x + k[2]) + k[3]) % P
        x2 = x * x
        e5 = ((x + k[2]) * ((x2 + k[4]) * (x2 + x + k[3]) + k[1]) + k[0]) % P
        nf += 1
        if e4 != g4 or e5 != g5:
            bad += 1; print("FIN MISMATCH", line.strip(), hex(e4), hex(e5))
        continue
    a, b, c, m, s, fo, ma = [int(t, 16) for t in f]
    n += 1
    if ma % P != (a * b + c) % P or ma >= 2**64: bad += 1; print("MULADD", line.strip(), hex((a*b+c) % P))
    if b >= P: bad += 1; print("b not canonical", line.strip())
    # mul / add outputs are non-canonical: compare modulo p; fold must be canonical and congruent
    if m % P != (a * b) % P or m >= 2**64: bad += 1; print("MUL", line.strip(), hex((a*b) % P))
    if s % P != (a + b) % P or s >= 2**64: bad += 1; print("ADD", line.strip(), hex((a+b) % P))
    if fo != a % P: bad += 1; print("FOLD", line.strip(), hex(a % P))
print(f"checked {n} (a,b) rows and {nf} finalizer rows, {bad} mismatches")
sys.exit(1 if bad else 0)
