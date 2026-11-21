"""Statement review of Remainder K (odinfree, M-1099, bp1_e12af376): own code, exact arithmetic.
Part A (r = 4, 5, every word): the counting bound |L| * C(5q, 4q+1) <= C(8q, 4q+1) for any list of distinct
  polynomials of degree <= 4q agreeing with the word on >= 5q of the n = 8q points, with the exact smallest K
  for which Remainder's two inequalities hold at that size.
Part B (r = 4, chosen words): the exact native list at agreement >= 10 of n = 16 in F_{p^2}, p = 2^31 - 1,
  D = all 16th roots of unity, by interpolating every 9-subset of D; on centre rows also the members whose
  error locator has the trinomial-block shape of the module (`blocks q i j`).
Usage: python3 -I sr_remainder.py
"""
import itertools, random
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

print("Part A: counting bound, every word, any field")
for r in (4, 5):
    n = 2**r; q = n // 8; k1 = 4*q + 1; a = 5*q
    bound = comb(n, k1) // comb(a, k1)
    exact = Fraction(comb(n, k1), comb(a, k1))
    allowance = 1144 if r == 4 else 496248
    kmin = -(-(bound + allowance) // n)        # smallest K with bound + allowance <= K n
    print(f"  r={r} n={n}: C({n},{k1})/C({a},{k1}) = {exact} -> |L| <= {bound}; allowance {allowance};"
          f" Remainder K holds at this size for every K >= {kmin}; K = 2^20 gives K n = {2**20*n}")

print("Part B: exact native lists at n = 16 over F_{p^2}, p = 2^31 - 1")
order = p*p - 1
g = None
for c in range(2, 200):                     # a primitive 16th root of unity
    cand = pw((c, 1), order // 16)
    if pw(cand, 8) != ONE: g = cand; break
D = [pw(g, j) for j in range(16)]
assert len(set(D)) == 16 and all(pw(x, 16) == ONE for x in D)
n, q = 16, 2; K4 = 4*q                       # degree <= 8, agreement >= 10, errors <= 6

def evalp(cf, x):
    r = ZERO
    for c in reversed(cf): r = add(mul(r, x), c)
    return r
def interp(xs, ys):                          # coefficients of the degree <= len-1 interpolant
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
def locator(U):
    cf = [ONE]
    for x in U:
        cf = [sub((cf[t-1] if t else ZERO), mul(x, cf[t] if t < len(cf) else ZERO)) for t in range(len(cf)+1)]
    return cf
def is_block(U):                              # (prod (X - x)) = a + bX^i + cX^(i+j) + X^(2q)(s + tX^j + X^(i+j))
    L = locator(U); deg = len(L) - 1
    for i in range(1, q+1):
        for j in range(1, q+1-i):
            if deg != 2*q + i + j: continue
            want = {0, i, i+j, 2*q, 2*q+j, 2*q+i+j}
            if all((L[t] != ZERO) == (t in want) for t in range(deg+1)) and L[deg] == ONE:
                return True
    return False

def native_list(word):
    ys = [evalp(word, x) for x in D]
    seen = {}
    for S in itertools.combinations(range(16), K4 + 1):
        cf = interp([D[s] for s in S], [ys[s] for s in S])
        key = tuple(cf)
        if key in seen: continue
        if add(cf[0], cf[K4]) != ZERO: seen[key] = None; continue      # not native
        U = [D[t] for t in range(16) if evalp(cf, D[t]) != ys[t]]
        seen[key] = U if len(U) <= 3*q else None
    return [U for U in seen.values() if U is not None]

rng = random.Random(20261121)
def rnd(): return (rng.randrange(p), rng.randrange(p))
def word(terms, R):
    cf = [ZERO]*16
    for e, c in terms: cf[e] = add(cf[e], c)
    for t, c in enumerate(R): cf[t] = add(cf[t], c)
    return cf
cases = [("X^12 (centre, R = 0)", [(12, ONE)], []),
         ("X^12 + R, R random deg <= 8 (centre)", [(12, ONE)], [rnd() for _ in range(9)]),
         ("X^9 + X^11 + X^15, R = 0", [(9, ONE), (11, ONE), (15, ONE)], []),
         ("X^10 + X^14, R = 0", [(10, ONE), (14, ONE)], [])]
for _ in range(3):
    ms = rng.sample(range(9, 16), 3)
    cases.append((f"random trinomial exponents {sorted(ms)}, random coefficients and R", [(m, rnd()) for m in ms], [rnd() for _ in range(9)]))
for name, terms, R in cases:
    w = word(terms, R)
    Ls = native_list(w)
    centre = all(e == 12 for e, _ in terms)
    nb = sum(1 for U in Ls if is_block(U)) if centre else 0
    print(f"  {name}: native list {len(Ls)} (bound 1144){'; block-shaped members ' + str(nb) + ', remainder list ' + str(len(Ls)-nb) if centre else ''}")
print("done")
