"""Statement review of PrefixCount C0 (py2755, bp1_8ea1a968, InteriorThree_PrefixCount.lean): own code, exact
arithmetic, the two smallest sizes the statement admits (r = 4, 5).
Reading: for every reached row and key, PrefixCount asks for SOME Valid rule and relabelling pi such that the eligible
masks have at most C0 n distinct tags. With rule .blocks {} (Blocks D h {} holds; `passes` then accepts every mask, since
clean {} U = {} and 0 < threshold) and pi = identity, the tags are at most the eligible masks, and each eligible mask is
errors D P w of a `good` P (deg P <= 4q, at most 3q errors). Distinct masks come from distinct P.
Part A (every row, key, r = 4, 5): #good P <= C(8q, 4q+1)/C(5q, 4q+1), compared with C0 n, C0 = 174762.
Part B (n = 16, every mask): group all subsets U of mu_16 of weight 5 and 6 (2q < u <= 3q) by tag = (u, the top
width = floor((8q - u)/3) + 1 coefficients of prod_{x in U}(X - x), the leading 1 included), over F_{p^2}, p = 2^31 - 1;
report the fibre sizes (LocatorPrefix.three says at most 3).
Usage: python3 -I sr_prefixcount.py
"""
import itertools, collections
from math import comb
from fractions import Fraction

p = 2**31 - 1
def add(a, b): return ((a[0]+b[0]) % p, (a[1]+b[1]) % p)
def sub(a, b): return ((a[0]-b[0]) % p, (a[1]-b[1]) % p)
def mul(a, b): return ((a[0]*b[0]-a[1]*b[1]) % p, (a[0]*b[1]+a[1]*b[0]) % p)
def pw(a, e):
    r = (1, 0)
    while e:
        if e & 1: r = mul(r, a)
        a = mul(a, a); e >>= 1
    return r
ZERO, ONE = (0, 0), (1, 0)
C0 = 174762

print("Part A: counting bound, every reached row and key, rule .blocks {}, identity relabelling")
for r in (4, 5):
    n = 2**r; q = n // 8; k1 = 4*q + 1
    b = Fraction(comb(n, k1), comb(5*q, k1))
    print(f"  r={r} n={n}: #records <= #masks <= #good words <= C({n},{k1})/C({5*q},{k1}) = {b}; C0 n = {C0*n}; holds: {b <= C0*n}")

print("Part B: record fibres of all heavy masks at n = 16 over F_{p^2}")
order = p*p - 1
g = next(c for c in ((pw((c, 1), order // 16)) for c in range(2, 200)) if pw(c, 8) != ONE)
D = [pw(g, j) for j in range(16)]
assert len(set(D)) == 16 and all(pw(x, 16) == ONE for x in D)
q = 2
def locator(U):
    cf = [ONE]
    for x in U:
        cf = [sub((cf[t-1] if t else ZERO), mul(x, cf[t] if t < len(cf) else ZERO)) for t in range(len(cf)+1)]
    return cf
for u in range(2*q + 1, 3*q + 1):
    width = (8*q - u)//3 + 1
    fib = collections.Counter()
    total = 0
    for S in itertools.combinations(range(16), u):
        L = locator([D[s] for s in S]); total += 1
        fib[(u, tuple(L[j] for j in range(u - width + 1, u + 1)))] += 1
    sizes = sorted(collections.Counter(fib.values()).items())
    print(f"  weight {u}: {total} masks (C(16,{u}) = {comb(16, u)}), width {width}, {len(fib)} records, fibre sizes (size, count): {sizes}")
print("done")
