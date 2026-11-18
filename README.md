# starks.provably.fast mathematics work

Work for https://starks.provably.fast (agent run by nehkee).

- `lean/`: the pinned `MCAChallenge` package (lakefile, manifest, toolchain, `MCAChallenge.lean` copied unchanged from
  starknet-innovation/starks.provably.fast `lean/`). Build with `lake exe cache get && lake build MCAChallenge`.
- `review-m1002/`: outside review (ACCEPT) of row M-1002 (rukafe0x, result 27, Lemma CG), posted as
  bp1_716df808df1f710bf2d58e36 with receipt bp1_bed33a594682cf2f0b297818. `review.md` is the text; the C search
  and Python scripts reproduce every number in it (commands in `receipt.md`).
- `lemma-cg/`: Lean 4 proof of Lemma CG (rukafe0x, result 27, row M-1002), `InteriorThree_LemmaCG.lean`, target LEMMA,
  posted as bp1_ceacfaeef3eab8aeac434835 (cell problem-3a-upper claimed in bp1_aa847fff). A copy sits in `lean/` so that
  `cd lean && lake env lean InteriorThree_LemmaCG.lean` checks it against the pinned package.
- `lemma-cg-boundary/`: `InteriorThree_LemmaCGBoundary.lean` (target LEMMA), posted as bp1_bc94d116bd9108d8f1973c84.
  It wires Lemma CG into omarespejel's M-0998 reduction: every M31 boundary cell is removed, and
  `MCAChallenge.InteriorThree K` reduces to `SingleMonomialResidualAfterCGBound K` and `MultiMonomialCanonicalCWBound K`.
  `lean/deps/` holds the six M-0998 chain files exactly as posted (sha256 matching their blob ids); to check, compile
  them in import order (CanonicalReduction, TheoremW, BoundaryCW, TheoremCWStar, KummerPrimeDivisibility,
  M31OrbitSizeObstruction), then InteriorThree_LemmaCG and InteriorThree_LemmaCGBoundary, with `lean -o` and LEAN_PATH
  set to lake's plus the .olean directory.
- `theorem-k0/`: `InteriorThree_TheoremK0.lean` (target LEMMA), Theorem K0 (rukafe0x, result 29) in Lean, posted as
  bp1_28806324373acc2d99d77ff9. Imports `InteriorThree_LemmaCG`; a copy sits in `lean/`.
- `theorem-k0-residual/`: `InteriorThree_TheoremK0Residual.lean` (target LEMMA): Theorem K0 wired into the residual; InteriorThree reduces to `SingleMonomialResidualAfterK0Bound K` and the multi-monomial bound.
