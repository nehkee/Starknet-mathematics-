"""Build every module in SRC in dependency order (REPLAY_WORKERS, default 4), then leanchecker and an axiom audit
for the queue modules. Our own code; it only reads the untrusted files to find their import lines."""
import json, re, subprocess, sys, os, time
from concurrent.futures import ThreadPoolExecutor
SP, LP, TC = sys.argv[1], sys.argv[2], sys.argv[3]
WORKERS = int(os.environ.get("REPLAY_WORKERS", "4"))  # lower it for memory-heavy closures
WRAP = [SP + '/tools/sandboxed.sh']
assert os.access(WRAP[0], os.X_OK), 'sandbox wrapper missing: refusing to compile untrusted files'
SRC, OL, LOG, AUD = (SP + '/replays/' + d for d in ('src', 'olean', 'logs', 'audit'))
mods = sorted(f[:-5] for f in os.listdir(SRC) if f.endswith('.lean'))
deps = {}
for m in mods:
    ds = set()
    for line in open(f'{SRC}/{m}.lean'):
        mm = re.match(r'\s*(?:public\s+)?import\s+(\S+)', line)
        if mm and mm.group(1) in mods: ds.add(mm.group(1))
    deps[m] = ds
env = dict(os.environ, LEAN_PATH=LP + ':' + OL, PATH=TC + ':' + os.environ['PATH'])
res = {}
def build(m):
    t = time.time()
    if os.path.exists(f'{OL}/{m}.olean') and os.path.exists(f'{LOG}/{m}.build.log'):
        out = open(f'{LOG}/{m}.build.log').read()
        return m, 0, len(re.findall(r': error', out)), len(re.findall(r': warning', out)), 0.0
    r = subprocess.run(WRAP + ['lean', '-o', f'{OL}/{m}.olean', f'{SRC}/{m}.lean'], capture_output=True, text=True, env=env, cwd=SP + '/replays')
    out = r.stdout + r.stderr
    open(f'{LOG}/{m}.build.log', 'w').write(out)
    errs = len(re.findall(r': error', out)); warns = len(re.findall(r': warning', out))
    return m, r.returncode, errs, warns, round(time.time() - t, 1)
done, failed = set(), set()
with ThreadPoolExecutor(WORKERS) as ex:
    while len(done) + len(failed) < len(mods):
        ready = [m for m in mods if m not in done and m not in failed and deps[m] <= done]
        blocked = [m for m in mods if m not in done and m not in failed and deps[m] & failed]
        for m in blocked: failed.add(m); res[m] = (m, 'blocked', 0, 0, 0)
        if not ready:
            if blocked: continue
            print('cycle or stuck', [m for m in mods if m not in done and m not in failed]); break
        for m, rc, e, w, t in ex.map(build, ready):
            res[m] = (m, rc, e, w, t)
            (done if rc == 0 and e == 0 else failed).add(m)
        print(f'built {len(done)} failed {len(failed)} / {len(mods)}', flush=True)
q = json.load(open(SP + '/replay_index.json'))['q']
qmods = sorted({n[:-5] for _, n, _ in q})
def check(m):
    if m not in done: return m, None, None
    r = subprocess.run(WRAP + ['leanchecker', m], capture_output=True, text=True, env=env, cwd=SP + '/replays')
    lc = (r.returncode, (r.stdout + r.stderr).strip())
    aud = f'{AUD}/audit_{m}.lean'
    open(aud, 'w').write(f'''import {m}
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `{m} | throwError "module not found"
  let names := env.header.moduleData[idx.toNat]!.constNames
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  for n in names do
    for a in (← collectAxioms n) do
      if !(std.contains a) then bad := bad.push (n, a)
  logInfo m!"AUDIT {m}: constants {{names.size}}, non-standard axiom uses {{bad.size}} {{bad.toList.take 5}}"
''')
    r2 = subprocess.run(WRAP + ['lean', aud], capture_output=True, text=True, env=env, cwd=SP + '/replays')
    return m, lc, (r2.stdout + r2.stderr).strip()
with ThreadPoolExecutor(WORKERS) as ex:
    checks = {m: (lc, au) for m, lc, au in ex.map(check, qmods)}
json.dump({'build': res, 'checks': checks, 'qmods': qmods}, open(SP + '/replays/results.json', 'w'), indent=1)
print('DONE', len(done), 'built,', len(failed), 'failed')
