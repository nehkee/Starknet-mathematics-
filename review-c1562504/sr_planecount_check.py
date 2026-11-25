"""Exact checks of sr_planecount output (PlaneCount review of bp1_c1562504, draft).

compare n k l b FILE : the candidate masks in FILE must equal the set of all error sets B of size b
                       with the coefficient gap, enumerated exactly by the reference (small n only).
verify  n k l b FILE : for every candidate in FILE, compute P = X^l mod L_A exactly and report
                       deg P, the exact agreement count, and whether B is the exact error set.
Run: python3 -I sr_planecount_check.py MODE n k l b FILE   (standard library only)
"""
import os
import sys
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sr_planecount_ref as R  # noqa: E402


def masks(path):
    return {int(line.split()[1], 16) for line in open(path) if line.startswith('candidate ')}


def gap_sets(D, k, l, b):
    n = len(D); d = l - (n - b); out = set()
    for B in combinations(range(n), b):
        LB = R.locator([D[i] for i in B]); LB += [R.ZERO] * (b + 1 - len(LB))
        if all(LB[b - j] == R.ZERO for j in range(d + 1, l - k + 1)):
            out.add(sum(1 << i for i in B))
    return out


def word(D, l, mask):
    n = len(D)
    B = [i for i in range(n) if mask >> i & 1]
    LB = R.locator([D[i] for i in B])
    Xn1 = [R.sub(R.ZERO, R.ONE)] + [R.ZERO] * (n - 1) + [R.ONE]
    LA, r = R.pdivmod(Xn1, LB); assert not r
    _, Pl = R.pdivmod([R.ZERO] * l + [R.ONE], LA)
    ag = R.agreement(D, Pl, l)
    return Pl, ag, B


def main():
    mode, n, k, l, b, path = sys.argv[1], *map(int, sys.argv[2:6]), sys.argv[6]
    D = R.grid(n); got = masks(path)
    if mode == 'rotclose':   # random mode seeds through point 1; the gap sets are closed under rotation
        full = (1 << n) - 1
        got = {((m << s) | (m >> (n - s))) & full for m in got for s in range(n)}
        mode = 'compare'
    if mode == 'compare':
        ref = gap_sets(D, k, l, b)
        print(f'compare n={n} k={k} l={l} b={b}: reference {len(ref)} sets, search {len(got)} sets, equal: {ref == got}')
        return 0 if ref == got else 1
    bad = 0
    for m in sorted(got):
        Pl, ag, B = word(D, l, m)
        exact = sorted(set(range(n)) - set(ag)) == B
        ok = len(Pl) <= k and len(ag) >= n - b
        bad += not ok
        print(f'mask {m:016x}: deg P = {len(Pl) - 1}, agreement {len(ag)}, exact error set: {exact}, valid: {ok}')
    print(f'verify n={n} k={k} l={l} b={b}: {len(got)} candidates, invalid {bad}')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
