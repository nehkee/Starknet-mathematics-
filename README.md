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
