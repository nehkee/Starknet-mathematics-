"""Exact reference for the PlaneCount search (review of bp1_c1562504, draft).

PlaneCount K (InteriorThree_EndpointQuartet.lean) counts, on one affine graph in the
endpoints, the polynomials P with deg P <= 4q-1 that agree with X^l on at least 5q
points of D = mu_n (n = 8q) in F = F_{p^2}, p = 2^31-1.  Every such fibre is a subset
of the full list of X^l, so the full list is an upper bound for every graph.

Reduction used by the search (checked here against brute force):
  P is on the list with exact agreement set A (|A| = a >= A0) and error set B
  (b = n - a) iff X^l - P = L_A * R with R monic of degree d = l - a, and that holds iff
  the locator L_B = prod_{x in B} (X - x) has zero coefficients at X^(b-j) for every
  j in [d+1, l-k], where k = number of coefficients of P (k = 4q).
  Then P = X^l mod L_A with L_A = (X^n - 1)/L_B.

Standard library only, exact arithmetic in F_{p^2} = F_p[i]/(i^2+1) (p = 3 mod 4).
Run: python3 -I sr_planecount_ref.py
"""
from itertools import combinations
import sys

P = 2**31 - 1
ZERO, ONE = (0, 0), (1, 0)


def add(a, b): return ((a[0] + b[0]) % P, (a[1] + b[1]) % P)
def sub(a, b): return ((a[0] - b[0]) % P, (a[1] - b[1]) % P)
def mul(a, b): return ((a[0] * b[0] - a[1] * b[1]) % P, (a[0] * b[1] + a[1] * b[0]) % P)


def pw(a, e):
    r = ONE
    while e:
        if e & 1: r = mul(r, a)
        a = mul(a, a); e >>= 1
    return r


def inv(a):
    nrm = (a[0] * a[0] + a[1] * a[1]) % P
    ni = pow(nrm, P - 2, P)
    return (a[0] * ni % P, (-a[1]) * ni % P)


def primitive_root_2_31():
    """Smallest t >= 1 such that w = (1 + t i)^(p-1) has order exactly 2^31 (p + 1 = 2^31)."""
    t = 1
    while True:
        w = pw((1, t), P - 1)
        if pw(w, 2**30) != ONE:
            assert pw(w, 2**31) == ONE
            return t, w
        t += 1


def grid(n):
    _, w = primitive_root_2_31()
    z = pw(w, 2**31 // n)
    pts = [pw(z, j) for j in range(n)]
    assert len(set(pts)) == n and pw(z, n) == ONE
    return pts


# polynomials: coefficient lists, low degree first
def trim(f):
    while f and f[-1] == ZERO: f.pop()
    return f


def pmul(f, g):
    r = [ZERO] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            r[i + j] = add(r[i + j], mul(a, b))
    return trim(r)


def pdivmod(f, g):
    f = list(f); g = trim(list(g)); q = [ZERO] * max(1, len(f) - len(g) + 1)
    li = inv(g[-1])
    while len(trim(f)) >= len(g):
        s = len(f) - len(g); c = mul(f[-1], li); q[s] = c
        for i, b in enumerate(g): f[s + i] = sub(f[s + i], mul(c, b))
        trim(f)
    return trim(q), f


def peval(f, x):
    r = ZERO
    for c in reversed(f): r = add(mul(r, x), c)
    return r


def locator(pts):
    f = [ONE]
    for x in pts: f = pmul(f, [sub(ZERO, x), ONE])
    return f


def interpolate(xs, ys):
    """Lagrange interpolation, degree < len(xs)."""
    m = len(xs); res = [ZERO] * m
    for i in range(m):
        num = [ONE]; den = ONE
        for j in range(m):
            if j != i:
                num = pmul(num, [sub(ZERO, xs[j]), ONE]); den = mul(den, sub(xs[i], xs[j]))
        c = mul(ys[i], inv(den))
        for t, v in enumerate(num): res[t] = add(res[t], mul(c, v))
    return trim(res)


def agreement(D, f, l):
    return [i for i, x in enumerate(D) if peval(f, x) == pw(x, l)]


def brute(D, k, l, A0):
    """Every P with deg P < k and >= A0 agreements is the interpolant of X^l on some k of them."""
    ys = [pw(x, l) for x in D]; found = {}
    for S in combinations(range(len(D)), k):
        f = interpolate([D[i] for i in S], [ys[i] for i in S])
        ag = agreement(D, f, l)
        if len(ag) >= A0: found[tuple(f)] = tuple(ag)
    return found


def by_gap(D, k, l, A0):
    """Enumerate error sets B with the coefficient gap; return exact list and run the double check."""
    n = len(D); found = {}; checked = 0
    for a in range(A0, l + 1):
        b = n - a; d = l - a
        for B in combinations(range(n), b):
            LB = locator([D[i] for i in B]); LB += [ZERO] * (b + 1 - len(LB))
            gap = all(LB[b - j] == ZERO for j in range(d + 1, l - k + 1))
            Xn1 = [sub(ZERO, ONE)] + [ZERO] * (n - 1) + [ONE]
            LA, r = pdivmod(Xn1, LB); assert not r
            _, Pl = pdivmod([ZERO] * l + [ONE], LA)
            assert gap == (len(Pl) <= k), (B, gap, len(Pl))   # the reduction, both directions
            checked += 1
            if gap:
                ag = agreement(D, Pl, l)
                assert set(ag) >= set(range(n)) - set(B)
                if set(ag) == set(range(n)) - set(B): found[tuple(Pl)] = tuple(ag)
    return found, checked


def main():
    out = []
    t, _ = primitive_root_2_31()
    out.append(f'p = 2^31-1, F_(p^2) = F_p[i]/(i^2+1), generator of mu_(2^31): (1 + {t} i)^(p-1)')
    # rate 1/2 with the PlaneCount agreement (empty lists) and lower rates with non-empty lists
    for (n, k, l, A0) in [(16, 8, 10, 10), (16, 8, 11, 10), (16, 8, 12, 9), (16, 6, 8, 7), (16, 6, 10, 7),
                          (16, 6, 12, 8), (16, 6, 13, 7), (16, 4, 9, 5), (16, 4, 11, 6)]:
        D = grid(n)
        bf = brute(D, k, l, A0)
        gp, checked = by_gap(D, k, l, A0)
        ok = set(bf) == set(gp)
        out.append(f'n={n} k={k} l={l} agreement>={A0}: brute force {len(bf)} words, gap reduction {len(gp)} words '
                   f'({checked} error sets tested, gap <=> deg(X^l mod L_A) < k on all), equal: {ok}')
        assert ok
    print('\n'.join(out))


if __name__ == '__main__':
    sys.exit(main())
