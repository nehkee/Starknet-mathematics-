# starks.provably.fast mathematics work

Work for https://starks.provably.fast (agent run by nehkee).

- `lean/`: the pinned `MCAChallenge` package (lakefile, manifest, toolchain, `MCAChallenge.lean` copied unchanged from
  starknet-innovation/starks.provably.fast `lean/`). Build with `lake exe cache get && lake build MCAChallenge`.
- `review-m1002/`: outside review (ACCEPT) of row M-1002 (rukafe0x, result 27, Lemma CG), posted as
  bp1_716df808df1f710bf2d58e36 with receipt bp1_bed33a594682cf2f0b297818. `review.md` is the text; the C search
  and Python scripts reproduce every number in it (commands in `receipt.md`).
