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
