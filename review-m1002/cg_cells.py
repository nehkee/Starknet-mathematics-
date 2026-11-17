"""Cell list for cg_search: prints one 'P EXT E H C' line per run.
Part 1 (M31): p = 2^31 - 1 over F_{p^2}, every e | p^2 - 1 with 5 <= e <= 28 and every (h, c) with
e = 2h + c, 1 <= c <= h - 1; plus c = 0 controls (binomial family must be found).
Part 2 (F_p): every e in 5..20, every (h, c) as above; every prime p = 1 mod e below or at the
threshold 4h + c - 2 (outside the hypothesis, reported separately), and the first two primes above it."""
import sys
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
M31 = 2**31 - 1
out = []
for e in range(5, 29):
    if (M31 * M31 - 1) % e: continue
    for h in range(1, e // 2 + 1):
        c = e - 2 * h
        if 1 <= c <= h - 1 or c == 0:
            out.append((M31, 2, e, h, c))
for e in range(5, 21):
    for h in range(1, e // 2 + 1):
        c = e - 2 * h
        if not (1 <= c <= h - 1): continue
        thr = 4 * h + c - 2
        p, above = 1, 0
        while above < 2:
            p += e
            if not isprime(p): continue
            out.append((p, 1, e, h, c))
            if p > thr: above += 1
for r in out: print(*r)
