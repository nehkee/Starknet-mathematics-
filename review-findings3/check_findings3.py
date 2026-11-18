"""Independent check of bp1_73d89440 (ardianreffa, three findings on M-0526, M-0521, M-0524).
Exact arithmetic (fractions), standard library only. Own code; none of the post's code is run.
Johnson scheme J(v, w): distance x = |A minus B|. Dual eigenvalues (Hahn polynomials):
  Q_k(x) = m_k * sum_j (-1)^j C(k,j) C(v+1-k,j) / (C(w,j) C(v-w,j)) * C(x,j),  m_k = C(v,k) - C(v,k-1).
Usage: python3 -I check_findings3.py PATH/dc_32_12_7.json
"""
import sys, json, itertools, hashlib
from fractions import Fraction as Fr
from math import comb

def m(v, k): return comb(v, k) - (comb(v, k - 1) if k else 0)
def Q(v, w, k, x):
    return m(v, k) * sum(Fr((-1) ** j * comb(k, j) * comb(v + 1 - k, j), comb(w, j) * comb(v - w, j)) * comb(x, j)
                         for j in range(0, k + 1))

out = []
def say(s): out.append(s); print(s)

# sanity: Q_k(0) = m_k, and the orthogonality-type check sum_x n_x Q_k(x) = 0 for k >= 1
def nx(v, w, x): return comb(w, x) * comb(v - w, x)
for (v, w) in [(32, 12), (18, 3), (20, 3), (32, 9)]:
    assert all(Q(v, w, k, 0) == m(v, k) for k in range(w + 1))
    assert all(sum(nx(v, w, x) * Q(v, w, k, x) for x in range(w + 1)) == 0 for k in range(1, w + 1))
say("sanity: Q_k(0) = m_k and sum_x n_x Q_k(x) = 0 (k >= 1) for J(32,12), J(18,3), J(20,3), J(32,9): ok")

# ---- item 1: c = 23 cores <-> 9-point complements meeting in <= 1 point
say("item 1:")
say(f"  |A^c ∩ B^c| = 32 - 46 + |A ∩ B|: |A∩B| <= 15 <=> |A^c ∩ B^c| <= 1: {all((32-46+t <= 1) == (t <= 15) for t in range(14, 24))}")
# LP for 9-sets in 32 points meeting in <= 1 point: x = 9 - |A∩B| in {8, 9}
def lp2(v, w, xs):
    """max 1 + sum A_x (x in xs, two variables) s.t. m_k + sum A_x Q_k(x) >= 0, A >= 0; exact vertex enumeration."""
    cons = [[Q(v, w, k, x) for x in xs] + [Fr(m(v, k))] for k in range(1, w + 1)]
    cons += [[Fr(1), Fr(0), Fr(0)], [Fr(0), Fr(1), Fr(0)]]          # A >= 0
    best = None
    for c1, c2 in itertools.combinations(cons, 2):
        det = c1[0] * c2[1] - c1[1] * c2[0]
        if det == 0: continue
        a = (-c1[2] * c2[1] + c2[2] * c1[1]) / det
        b = (-c1[0] * c2[2] + c2[0] * c1[2]) / det
        if all(c[0] * a + c[1] * b + c[2] >= 0 for c in cons):
            val = 1 + a + b
            best = val if best is None or val > best else best
    return best
lp9 = lp2(32, 9, [8, 9])
say(f"  Delsarte LP, 9-sets of 32 points meeting in <= 1 point: {lp9} (floor {lp9.numerator // lp9.denominator}); post: 256/49, floor 5")
cnt = lambda N: 9 * N - comb(N, 2)
say(f"  point count 9N - C(N,2): N=4 -> {cnt(4)} <= 32, N=5 -> {cnt(5)} > 32, so N <= 4")
fam = [{0,1,2,6,7,8,9,10,11}, {0,3,4,12,13,14,15,16,17}, {1,3,5,18,19,20,21,22,23}, {2,4,5,24,25,26,27,28,29}]
ok = all(len(s) == 9 for s in fam) and all(len(a & b) == 1 for a, b in itertools.combinations(fam, 2))
comp = [set(range(32)) - s for s in fam]
ok2 = all(len(s) == 23 for s in comp) and all(len(a & b) == 15 for a, b in itertools.combinations(comp, 2))
say(f"  the posted family: four 9-sets, pairwise meeting in exactly 1 point: {ok}; complements are 23-sets meeting pairwise in 15: {ok2}")
say(f"  c >= 23 line: 9 * 4 = {9*4} (row: 9 * 5 = 45)")

# ---- item 2: the posted dual certificate on J(32,12), intersections <= 7 (x = 12 - |A∩B| in 5..12)
say("item 2:")
path = sys.argv[1]
raw = open(path, 'rb').read()
say(f"  dc_32_12_7.json sha256 {hashlib.sha256(raw).hexdigest()}")
dc = json.loads(raw)
v, w = dc["v"], dc["w"]
y = [Fr(t) for t in dc["y"]]
bound = 1 + sum(y[k - 1] * m(v, k) for k in range(1, w + 1))
say(f"  bound 1 + sum y_k m_k = {bound} = {float(bound):.6f}; post: 2643062642831/229000000 -> {bound == Fr(2643062642831, 229000000)}")
for x in range(1, w + 1):
    val = 1 + sum(y[k - 1] * Q(v, w, k, x) for k in range(1, w + 1))
    tag = "allowed" if x >= 5 else "excluded"
    say(f"  x = {x:2d} ({tag}): 1 + sum y_k Q_k(x) = {val}  (= {float(val):.6f})")
say(f"  y >= 0: {all(t >= 0 for t in y)}")
opt = Fr(2643060, 229) ; say(f"  (bound - 1) == (2643060/229 - 1) * 1.000001: {bound - 1 == (opt - 1) * Fr(1000001, 1000000)}")

# ---- item 3: triples on v points meeting pairwise in <= 1 point (J(v,3), x in {2,3})
say("item 3:")
for vv in (18, 20):
    val = lp2(vv, 3, [2, 3])
    say(f"  Delsarte LP J({vv},3), x in {{2,3}}: {val}; counting step v*floor((v-1)/2)/3 = {Fr(vv * ((vv - 1) // 2), 3)}")
blocks = set()
for base in ({0, 1, 4}, {0, 2, 9}, {0, 5, 11}):
    for t in range(19):
        blocks.add(frozenset((b + t) % 19 for b in base))
pairs_ok = all(sum(1 for B in blocks if p <= B) == 1 for p in map(frozenset, itertools.combinations(range(19), 2)))
avoid = [B for B in blocks if 18 not in B]
meet_ok = all(len(a & b) <= 1 for a, b in itertools.combinations(avoid, 2))
say(f"  cyclic STS(19), base blocks {{0,1,4}},{{0,2,9}},{{0,5,11}}: {len(blocks)} triples; every pair in exactly one: {pairs_ok}")
say(f"  triples avoiding point 18: {len(avoid)}, on 18 points, pairwise meeting <= 1: {meet_ok}")
