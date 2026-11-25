"""Coverage of the n = 64 line-mode search (PlaneCount review of bp1_c1562504, draft).

For each admissible l and error size b: u = 2b + k - n unknown locator coefficients; a seed is
point 0 plus u-2 distinct random points of the other n-1, and the search finds every error set B
that contains the seed.  A fixed B containing point 0 (every list member has a rotation that does)
is caught by one seed with probability c = C(b-1, u-2)/C(n-1, u-2); the job used N = ceil(4/c)
seeds, so B is missed with probability (1-c)^N <= exp(-cN) <= exp(-4).
Run: python3 -I sr_planecount_coverage.py   (standard library only, exact fractions)
"""
from fractions import Fraction
from math import comb, exp

n, q = 64, 8
k = 4 * q
total = 0
print(f'n={n} q={q} k={k}: admissible l with 5q < l and 2(l+1)+q <= 12q:',
      [l for l in range(n) if 5 * q < l and 2 * (l + 1) + q <= 12 * q])
print(f'counting bound C(n,4q)/C(5q,4q) = {Fraction(comb(n, 4 * q), comb(5 * q, 4 * q))}  vs  2^20*n = {2**20 * n}')
for l in (41, 42, 43):
    for b in range(n - l, n - 5 * q + 1):
        u = 2 * b + k - n
        c = Fraction(comb(b - 1, u - 2), comb(n - 1, u - 2))
        N = -(-4 * c.denominator // c.numerator)   # exact ceil(4/c)
        total += N
        print(f'l={l} b={b} u={u} seed points={u - 1} per-seed catch c={float(c):.4e} seeds N={N} '
              f'cN >= 4 (exact): {c * N >= 4}, so miss <= (1-c)^N <= e^-cN <= e^-4 = {exp(-4):.4f}')
print(f'total seeds {total}')
