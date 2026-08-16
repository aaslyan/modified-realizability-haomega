import re, glob, os
defs = {}
for path in sorted(glob.glob("HAomega/*.lean")):
    src = open(path).read()
    for m in re.finditer(r'^(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z_][\w.\']*)', src, re.M):
        nxt = re.search(r'^(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|end)\s', src[m.end():], re.M)
        end = m.end() + (nxt.start() if nxt else 1500)
        defs.setdefault(m.group(1), (os.path.basename(path), src[m.start():end]))
def reaches(n, seen=None, d=0):
    if seen is None: seen=set()
    if n in seen or d>7 or n not in defs: return None
    seen.add(n); _,b = defs[n]
    if 'extractClosed' in b: return 'EXTRACT'
    if '.eval Env.nil' in b: return 'Tm.eval'
    for c in set(re.findall(r'\b([A-Za-z_][\w.\']{2,})',b)):
        if c!=n and (r:=reaches(c,seen,d+1)): return r
    return None
tot={'EXTRACT':0,'Tm.eval':0,'PLAIN':0}; per={}
for path in sorted(glob.glob("HAomega/*.lean")):
    gs=[l for l in open(path).read().splitlines() if re.match(r'\s*#(guard|eval)\b',l)]
    if not gs: continue
    v={'EXTRACT':0,'Tm.eval':0,'PLAIN':0}
    for l in gs:
        best=None
        for h in set(re.findall(r'\b([A-Za-z_][\w.\']{2,})',l)):
            if h in defs and (r:=reaches(h)):
                best='EXTRACT' if r=='EXTRACT' else (best or 'Tm.eval')
        v[best or 'PLAIN']+=1
    for k in tot: tot[k]+=v[k]
    per[os.path.basename(path)]=v
print("TOTALS:", tot, "sum:", sum(tot.values()))
for f,v in sorted(per.items()): print(f"{f:32} {v}")
