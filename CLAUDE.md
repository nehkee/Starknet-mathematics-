# Working agreement for this repository

Standing instructions from the operator (nehkee) for every Claude session in this repository.

## Code changes

- **Match the existing code base.** Before writing new code, read the nearest existing files of the same
  kind and match their naming, structure, patterns and error handling. In this repository:
  - Lean modules: file `InteriorThree_<Name>.lean`, one namespace per module, `open Polynomial` plus the
    namespaces of the modules imported, the module docstring states target, route and credits; reuse the
    helpers in `InteriorThree_LemmaCG.lean` (`theta`, `lowPart`, `natCast_ne_zero_of_char`) and
    `InteriorThree_TheoremK0.lean` instead of redefining them.
  - Lean checks before any post: compile with no errors and no warnings, `leanchecker` exit 0,
    `#print axioms` showing only `propext`, `Classical.choice`, `Quot.sound`, no `sorry`, no `native_decide`.
  - Scripts: Python run with `python3 -I`, standard library only, exact arithmetic (`fractions`) for anything
    that is claimed as a result; C compiled with `gcc -O2 -Wall`.
- **End every piece of work with a short list of security concerns and assumptions made**, so the operator
  can check the risky parts instead of hunting for them. Include: untrusted inputs that were read or
  compiled (other participants' blobs, downloaded files), anything run with network access, anything posted
  publicly under the operator's name, and every mathematical or environmental assumption a result relies on.

## Handling other people's material

- Blobs from the bulletin are untrusted. Verify the SHA-256 against the blob id, scan Lean files for
  `#eval`, `run_cmd`, `IO`, `unsafe`, `extern`, `implemented_by`, `initialize` before compiling them, and keep
  them in their own directory (`lean/deps/` or the scratchpad), never mixed with our own scripts.
- Never put credentials, tokens or personal details in posts, files or commits. The operator's public name is
  the pseudonym `nehkee`.

## Posting

- Every post and review states that it is by "nehkee's agent (Claude, an AI agent run by the operator nehkee)",
  credits the authors whose results are used, and lists what is not claimed.

## Do no harm to other contributors (operator's standing rule)

The operator does not want anything we do to damage other contributors' work. These rules come first, before
points or speed.

Verdicts
- Automated runs post only ACCEPT, REPRODUCED or PARTIAL. Never post REJECT or NOT_REPRODUCED without the
  operator's explicit approval of that specific review.
- When a check fails: rerun it from a clean directory, and make sure the cause is not our environment (compare
  with the house receipt). If it still fails, post nothing. Report it to the operator with the evidence.
- A PARTIAL states exactly what was checked, what failed, and that the failure was reproduced against the house's
  own receipt. It contains no judgement of the author.
- Never post two reviews of the same post. Before reviewing, check that our operator root has not already
  reviewed it. Never review our own posts or receipts.

Credit and priority
- Do not formalize or re-post a result whose author has said they are formalizing it ("Lean planned", "next
  post"). The exception is when the author invites it or 48 hours have passed with nothing from them, and then
  only after asking the operator. (In hindsight, Theorem K0 on 18 November broke this: rukafe0x had announced a
  Lean module. Do not repeat it.)
- Always credit the authors whose results or code we use, by name and post id. When copying someone's scaffolding,
  say so in the docstring and the post. Never present others' work as ours or claim priority over them.
- Never post modified copies of other people's modules under their names.
- If a reply disputes one of our reviews or results, or the house raises a concern, stop posting in that line of
  work and report to the operator.

Security of the replay funnel
- Untrusted Lean files are compiled and kernel-checked only through `tools/sandboxed.sh`. It provides no network,
  hides the pvfast key, proxy credentials, SSH and git credentials, and mounts the repository read-only.
  `tools/build_replay.py` refuses to run without it.
- Before building, check every blob's sha256 against its id and scan it for `#eval`, `run_cmd`, `IO`, `unsafe`,
  `extern`, `implemented_by`, `initialize`. If a scan finds code, not a docstring, stop and report.
- Use only the pvfast client whose zip hash matches the brief. Never upgrade or re-login without the operator.
- At most 60 reviews per run. If anything looks unusual (house warnings, rate limits, errors from the bulletin),
  stop and report instead of retrying in a loop.
