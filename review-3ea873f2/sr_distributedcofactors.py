"""Statement review of DistributedCofactors C0 (py2755, bp1_3ea873f2, InteriorThree_WindowCofactors.lean): own code,
exact arithmetic, the two smallest sizes the statement admits (r = 4, 5).
Reading: for every reached row w and key, every set I of positive-degree cofactors C1 = nativeCofactor D r v (errors D P w),
P `good` (deg P <= 4q, boundary, <= 3q errors) and the mask passing the occupancy, Johnson, bias and six-exponent tests,
has |I| <= C0 n. nativeCofactor D r v U depends only on the mask U, so distinct C1 come from distinct masks, hence from
distinct good P.
Part A (every row and key, r = 4, 5): #good P <= C(8q, 4q+1)/C(5q, 4q+1), compared with C0 n, C0 = 174762.
Part B (n = 16, exhaustive per row): for the canonical rows X^m, m = 10..14, and for X^9 + X^11 + X^15, X^10 + X^14,
X^12 + X^13 + X^14, over F_{p^2}, p = 2^31 - 1, count every P of degree <= 8 agreeing with the row on >= 10 of the
16 points of mu_16 (all 9-subsets interpolated), over all keys together: an upper bound on |I| for that row.
Usage: python3 -I sr_distributedcofactors.py
"""
import itertools
from math import comb
from fractions import Fraction

p = 2**31 - 1
def add(a, b): return ((a[0]+b[0]) % p, (a[1]+b[1]) % p)
def sub(a, b): return ((a[0]-b[0]) % p, (a[1]-b[1]) % p)
def mul(a, b): return ((a[0]*b[0]-a[1]*b[1]) % p, (a[0]*b[1]+a[1]*b[0]) % p)
def inv(a):
    n = (a[0]*a[0]+a[1]*a[1]) % p; ni = pow(n, p-2, p)
    return (a[0]*ni % p, (-a[1])*ni % p)
def pw(a, e):
    r = (1, 0)
    while e:
        if e & 1: r = mul(r, a)
        a = mul(a, a); e >>= 1
    return r
ZERO, ONE = (0, 0), (1, 0)
C0 = 174762

print("Part A: counting bound, every reached row and key")
for r in (4, 5):
    n = 2**r; q = n // 8; k1 = 4*q + 1
    b = Fraction(comb(n, k1), comb(5*q, k1))
    print(f"  r={r} n={n}: |I| <= #masks <= #good words <= {b}; C0 n = {C0*n}; holds: {b <= C0*n}")

print("Part B: all words with >= 10 agreements, degree <= 8, n = 16 over F_{p^2}")
order = p*p - 1
g = next(c for c in ((pw((c, 1), order // 16)) for c in range(2, 200)) if pw(c, 8) != ONE)
D = [pw(g, j) for j in range(16)]
assert len(set(D)) == 16 and all(pw(x, 16) == ONE for x in D)
def evalp(cf, x):
    r = ZERO
    for c in reversed(cf): r = add(mul(r, x), c)
    return r
def interp(xs, ys):
    m = len(xs); cf = [ZERO]*m
    for j in range(m):
        num = [ONE]; den = ONE
        for k in range(m):
            if k == j: continue
            num = [sub((num[t-1] if t else ZERO), mul(xs[k], num[t] if t < len(num) else ZERO)) for t in range(len(num)+1)]
            den = mul(den, sub(xs[j], xs[k]))
        s = mul(ys[j], inv(den))
        for t in range(m): cf[t] = add(cf[t], mul(s, num[t]))
    return cf
rows = [(f"X^{m}", [m]) for m in range(10, 15)] + [("X^9 + X^11 + X^15", [9, 11, 15]), ("X^10 + X^14", [10, 14]), ("X^12 + X^13 + X^14", [12, 13, 14])]
for name, ms in rows:
    ys = [None]*16
    for t, x in enumerate(D):
        v = ZERO
        for m in ms: v = add(v, pw(x, m))
        ys[t] = v
    words = set()
    for S in itertools.combinations(range(16), 9):
        cf = tuple(interp([D[s] for s in S], [ys[s] for s in S]))
        if cf in words: continue
        if sum(1 for t in range(16) if evalp(cf, D[t]) == ys[t]) >= 10: words.add(cf)
    print(f"  {name}: {len(words)} words (all keys), so |I| <= {len(words)} <= {C0*16}")
print("done")
