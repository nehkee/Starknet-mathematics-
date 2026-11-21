"""Statement review of ErasureCatalogue B (py2755, bp1_813a82d9, InteriorThree_ErasureCatalogue.lean): own code,
exact arithmetic, the two smallest sizes the statement admits (r = 4, 5).
Part A (every reached row and key, r = 4, 5): the post's kernel-checked lemma `from_prefix` turns PrefixCap at one size
(with relabelling fun u => pi (index u)) into CatalogueCap at that size. With rule .blocks {}, index = id and pi = identity,
PrefixCap holds when #good words <= B n (each eligible mask is the error set of a distinct good word, deg <= 4q,
<= 3q errors), and #good words <= C(8q, 4q+1)/C(5q, 4q+1). Compared with B n, B = 174762.
Part B (n = 16, q = 2, over F_{p^2}, p = 2^31 - 1, every mask of weight 5 and 6): pad the locator to degree N = 3q = 6
(weight 5: times (X - y), y the first grid point outside U), take a = its coefficients, and test `Covers D q a U`
literally: a(6) = 1, U inside the grid roots of branch q a t for t = a(0), and |D minus common| < 4 |votes|, with
trunk = sum_{j >= 3q - spanWidth + 1} a_j X^j, slope = sum_{j <= 3q - spanWidth} conj(a_{3q-j}) X^j,
spanWidth = floor(5q/3) + 1, conj = Frobenius x -> x^p. Also checks branch q a a(0) = T exactly.
Usage: python3 -I sr_erasurecatalogue.py
"""
import itertools, collections
from math import comb
from fractions import Fraction

p = 2**31 - 1
def add(a, b): return ((a[0]+b[0]) % p, (a[1]+b[1]) % p)
def sub(a, b): return ((a[0]-b[0]) % p, (a[1]-b[1]) % p)
def mul(a, b): return ((a[0]*b[0]-a[1]*b[1]) % p, (a[0]*b[1]+a[1]*b[0]) % p)
def conj(a): return (a[0], (-a[1]) % p)       # x^p on F_p[i]/(i^2+1)
def pw(a, e):
    r = (1, 0)
    while e:
        if e & 1: r = mul(r, a)
        a = mul(a, a); e >>= 1
    return r
ZERO, ONE = (0, 0), (1, 0)
assert pw((3, 5), p) == conj((3, 5))
B = 174762

print("Part A: from_prefix + counting, every reached row and key, rule .blocks {}, index = id, identity relabelling")
for r in (4, 5):
    n = 2**r; q = n // 8; k1 = 4*q + 1
    b = Fraction(comb(n, k1), comb(5*q, k1))
    print(f"  r={r} n={n}: entries needed <= eligible masks <= good words <= {b}; B n = {B*n}; holds: {b <= B*n}")

print("Part B: every heavy mask at n = 16 covered by its own padded entry")
order = p*p - 1
g = next(c for c in ((pw((c, 1), order // 16)) for c in range(2, 200)) if pw(c, 8) != ONE)
D = [pw(g, j) for j in range(16)]
assert len(set(D)) == 16 and all(pw(x, 16) == ONE for x in D)
q = 2; N = 3*q; sw = 5*q//3 + 1
def locator(U):
    cf = [ONE]
    for x in U:
        cf = [sub((cf[t-1] if t else ZERO), mul(x, cf[t] if t < len(cf) else ZERO)) for t in range(len(cf)+1)]
    return cf
def evalp(cf, x):
    r = ZERO
    for c in reversed(cf): r = add(mul(r, x), c)
    return r
stats = collections.Counter(); entries = set()
for u in (5, 6):
    for S in itertools.combinations(range(16), u):
        U = [D[s] for s in S]
        pad = U if u == N else U + [next(D[j] for j in range(16) if j not in S)]
        a = locator(pad)
        trunk = [a[j] if N < j + sw else ZERO for j in range(N + 1)]
        slope = [conj(a[N - j]) for j in range(N - sw + 1)]
        t = a[0]
        branch = [add(trunk[j], mul(t, slope[j]) if j < len(slope) else ZERO) for j in range(N + 1)]
        roots = {x for x in D if evalp(branch, x) == ZERO}
        common = {x for x in D if evalp(trunk, x) == ZERO and evalp(slope, x) == ZERO}
        votes = roots - common
        ok = a[N] == ONE and set(U) <= roots and 4*len(votes) > 16 - len(common)
        stats[(u, 'covered' if ok else 'NOT covered')] += 1
        stats[(u, 'branch = T' if branch == a else 'branch != T')] += 1
        entries.add((u, tuple(a[N - sw + 1:])))
for k in sorted(stats): print(f"  weight {k[0]}: {k[1]}: {stats[k]}")
print(f"  distinct entries used (index = weight, head): {len(entries)} for {comb(16,5)+comb(16,6)} masks")
print("done")
