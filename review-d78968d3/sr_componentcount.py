"""Statement review of ComponentCount H (py2755, bp1_d78968d3, InteriorThree_ParityModeWiring.lean): own code,
exact arithmetic, the two smallest sizes the statement admits (r = 4, 5).
Reading of the statement: with m = 2d + [odd], B is Feasible for (odd, X^d, key) exactly when B != 0 is the component
of opposite parity to m of a word P = assemble odd B Q, deg P <= n/2, whose even part meets the key, and which agrees
with X^m on >= 5q points of D (ParityComponents.agreement, x != 0). Distinct B give distinct P.
Part A (every m, every key, r = 4, 5): the counting bound #words <= C(8q, 4q+1)/C(5q, 4q+1), compared with H n, H = 16384.
Part B (r = 4, exhaustive): every P of degree <= 8 over F_{p^2}, p = 2^31 - 1, that agrees with X^m on >= 10 of the
16 points of mu_16 (interpolate every 9-subset), m = 10..14; count words, words with B != 0, and the largest number of
distinct nonzero B at one key (key gamma = P_0 + P_8, and key none = words with P_8 = 0, allowed only for m < 7q).
Usage: python3 -I sr_componentcount.py
"""
import itertools
from math import comb
from fractions import Fraction

p = 2**31 - 1                      # F_{p^2} = F_p[i]/(i^2 + 1), p = 3 mod 4
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
H = 16384

print("Part A: counting bound, every m in [5q, 7q], every key, any field")
for r in (4, 5):
    n = 2**r; q = n // 8; k1 = 4*q + 1; a = 5*q
    exact = Fraction(comb(n, k1), comb(a, k1))
    print(f"  r={r} n={n}: #words <= C({n},{k1})/C({a},{k1}) = {exact}; H n = {H*n}; holds: {exact <= H*n}")

print("Part B: exhaustive at n = 16 over F_{p^2}, p = 2^31 - 1")
order = p*p - 1
g = None
for c in range(2, 200):
    cand = pw((c, 1), order // 16)
    if pw(cand, 8) != ONE: g = cand; break
D = [pw(g, j) for j in range(16)]
assert len(set(D)) == 16 and all(pw(x, 16) == ONE for x in D)
n, q = 16, 2

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

for m in range(5*q, 7*q + 1):
    ys = [pw(x, m) for x in D]
    words = set()
    for S in itertools.combinations(range(16), 4*q + 1):
        cf = tuple(interp([D[s] for s in S], [ys[s] for s in S]))
        if cf in words: continue
        if sum(1 for t in range(16) if evalp(cf, D[t]) == ys[t]) >= 5*q: words.add(cf)
    opp = 1 - m % 2                                  # B = coefficients of parity opposite to m
    comp = lambda P: tuple(P[t] for t in range(opp, 4*q + 1, 2))
    nonzero = [P for P in words if any(c != ZERO for c in comp(P))]
    bykey = {}
    for P in nonzero:
        bykey.setdefault(('gamma', add(P[0], P[4*q])), set()).add(comp(P))
        if P[4*q] == ZERO and m < 7*q: bykey.setdefault(('none',), set()).add(comp(P))
    mx = max((len(v) for v in bykey.values()), default=0)
    print(f"  m={m}: words {len(words)}, with B != 0: {len(nonzero)}, keys with B != 0: {len(bykey)},"
          f" largest count of distinct B at one key: {mx} (H n = {H*n})")
print("done")
