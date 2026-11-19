import json, subprocess, sys
cli, tid, out = sys.argv[1:4]
seq = 0; posts = []
while True:
    r = subprocess.run(["python3","-I",cli,"remote","bulletin","thread",tid,"--after-seq",str(seq),"--format","json"],capture_output=True,text=True)
    d = json.loads(r.stdout)
    ps = d.get("posts") or []
    if not ps: break
    posts += ps
    ns = max(p["sequence"] for p in ps)
    if ns <= seq: break
    seq = ns
    print(len(posts), seq, file=sys.stderr)
json.dump(posts, open(out,"w"))
