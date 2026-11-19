import json, re, subprocess, hashlib, sys, os
SP, CLI = sys.argv[1], sys.argv[2]
idx = json.load(open(SP + '/replay_index.json'))
allf = idx['all']
src = SP + '/replays/src'
def fetch(blob, path):
    if os.path.exists(path): return
    r = subprocess.run(['python3', '-I', CLI, 'remote', 'bulletin', 'blob-get', blob], capture_output=True, text=True)
    c = json.loads(r.stdout)['content']
    h = hashlib.sha256(c.encode()).hexdigest()
    assert 'cas1_' + h == blob, (path, blob, h)
    open(path, 'w').write(c)
need = {}
todo = []
for pid, name, blob in idx['q']:
    mod = name[:-5]; need.setdefault(mod, blob); todo.append(mod)
    fetch(blob, f'{src}/{mod}.lean')
seen = set()
external = set()
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.add(m)
    for line in open(f'{src}/{m}.lean'):
        mm = re.match(r'\s*(?:public\s+)?import\s+(\S+)', line)
        if not mm: continue
        imp = mm.group(1)
        if imp.startswith(('Mathlib', 'MCAChallenge', 'ArkLib', 'Batteries', 'Aesop', 'Qq', 'Std', 'Lean', 'Init', 'CompPoly', 'VCVio')):
            continue
        if imp not in allf: external.add(imp); continue
        if imp not in need:
            vers = allf[imp]
            if len({v[2] for v in vers}) > 1: print('AMBIGUOUS', imp); continue
            need[imp] = vers[-1][2]
            fetch(need[imp], f'{src}/{imp}.lean')
        todo.append(imp)
print('modules fetched:', len(need), 'unresolved imports:', sorted(external))
json.dump(need, open(SP + '/replays/need.json', 'w'))
