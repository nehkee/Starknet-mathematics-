"""Corollary (item 2) of M-1002: arithmetic of every boundary cell 4h = N over M31, n = 2^r, 7 <= r <= 31.
Family (result 7): q = n/8, m = 5q + d with q/2 < d < q, N = 3q - d, e = 3d - q, f = 4(q - d),
k = h - f/2; boundary 4h = N; agreement m - h >= 5n/8 (d >= h); nontrivial cells k >= 1 (result 8).
Cells with 3h < e have R = 0, so B^3 = X^f A Q and B(0) = 0: no member (M-0934 quartic range); they are
counted apart. The remaining cells (3h >= e) are the boundary cells of results 8 and 12.
Checks, for every cell: e = 2h + 2k; 3 does not divide e; h > 2k (so c = 2k in [1, h-1], CG's range);
p > 4h (result 8's fibre lemma); p > 4h + 2k - 2 (CG's characteristic bound), p = 2^31 - 1."""
import sys
p = 2**31 - 1
total = 0
for r in range(7, 32):
    q = 2 ** (r - 3); cells = 0; worst = 0; quartic = 0
    # 4 | 3q - d  <=>  d = 3q mod 4 = 0 mod 4 (q >= 16)
    d0 = q // 2 + 1
    d0 += (-d0) % 4
    for d in range(d0, q, 4):
        N = 3 * q - d; h = N // 4; e = 3 * d - q; f = 4 * (q - d); k = h - f // 2
        if k < 1 or d < h: continue
        if 3 * h < e:
            quartic += 1; continue
        cells += 1
        assert e == 2 * h + 2 * k, (r, d)
        assert e % 3 != 0, (r, d)
        assert h > 2 * k, (r, d)
        assert 1 <= 2 * k <= h - 1
        assert 4 * h < p and 4 * h + 2 * k - 2 < p
        worst = max(worst, 4 * h + 2 * k - 2)
    total += cells
    print(f"n=2^{r}: boundary cells {cells} (plus {quartic} with 3h < e), max 4h+2k-2 = {worst} < p")
print("all assertions passed; total cells", total)
