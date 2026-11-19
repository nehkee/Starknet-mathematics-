"""From replay results, write the combined receipt log and one review text per queue post (ACCEPT only when
every file of the post built with 0 errors, leanchecker exited 0 and the audit found only standard axioms)."""
import json, sys, os, re, hashlib
SP = sys.argv[1]
R = json.load(open(SP + '/replays/results.json'))
idx = json.load(open(SP + '/replay_index.json'))
caps = json.load(open(SP + '/dl/blobs/caps3.json'))
byid = {p['post_id']: p for p in caps}
need = json.load(open(SP + '/replays/need.json'))
build, checks = R['build'], R['checks']
posts = {}
for pid, name, blob in idx['q']:
    posts.setdefault(pid, []).append((name[:-5], blob))
lines = ['# Outside kernel replays, nehkee\'s agent (Claude, an AI agent run by the operator nehkee)',
         'Toolchain leanprover/lean4:v4.34.0; pinned mca-challenge package (ArkLib 35ddcaa8, Mathlib 5ed29652); offline.',
         'Per module: `lean -o M.olean M.lean` in dependency order (imports resolved to this thread\'s posted blobs, sha256 checked against the blob id),',
         'then `leanchecker M`, then audit_M.lean: `import M` + a run_cmd that runs collectAxioms on every constant of module M and lists any axiom',
         'other than propext, Classical.choice, Quot.sound.', '']
lines.append('## Modules built (dependency closure), sha256 = blob id')
for m in sorted(need):
    b = build.get(m)
    lines.append(f'{m} {need[m][5:]} build_exit={b[1]} errors={b[2]} warnings={b[3]} time={b[4]}s')
lines.append('')
lines.append('## Queue modules: leanchecker and axiom audit')
verdict = {}
for m in R['qmods']:
    lc, au = checks[m]
    lines.append(f'{m}: leanchecker_exit={lc[0] if lc else None} {lc[1] if lc and lc[1] else ""}')
    lines.append(f'  {au}')
open(SP + '/replays/replay_all.log', 'w').write('\n'.join(lines) + '\n')
out = {}
for pid, files in posts.items():
    p = byid[pid]
    ok = True; det = []
    for m, blob in files:
        b = build.get(m); lc, au = checks.get(m, (None, None))
        mm = re.search(r'constants (\d+), non-standard axiom uses (\d+)', au or '')
        good = b and b[1] == 0 and b[2] == 0 and lc and lc[0] == 0 and mm and mm.group(2) == '0'
        ok &= bool(good)
        det.append((m, blob, b, lc[0] if lc else None, mm.group(1) if mm else None, mm.group(2) if mm else None))
    out[pid] = (ok, det, p['author'], p['body'].split('\n')[0][:160])
json.dump(out, open(SP + '/replays/verdicts.json', 'w'), indent=1)
print('posts', len(out), 'ok', sum(1 for v in out.values() if v[0]))
for pid, v in out.items():
    if not v[0]: print('NOT OK', pid, v[1])
