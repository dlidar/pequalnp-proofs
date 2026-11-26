from pathlib import Path
from itertools import combinations
import json,subprocess,fcntl,sys
d=Path(__file__).resolve().parent
import shutil
solver=shutil.which("cadical") or next(Path("work/lean-runtime/toolchains").glob("*/bin/cadical")).resolve()
m=1885146376704737940
rows=[(1<<i)|(1<<(8+j)) for i in range(8) for j in range(8)]
def encode(count):
    clauses=[]
    nvars=0
    def var():
        nonlocal nvars
        nvars+=1
        return nvars
    def one(items):
        clauses.append(items)
        clauses.extend([-i,-j] for i,j in combinations(items,2))
    traces=[[var() for _ in rows] for _ in range(16+count)]
    for i in range(16):
        clauses.extend([v if r>>i&1 else -v] for v,r in zip(traces[i],rows))
    selectors=[]
    for i in range(16,16+count):
        op=var(); sel=[]; terms=[]
        for side in range(2):
            choice=[var() for _ in range(i)];one(choice);sel.append(choice)
            term=[var() for _ in rows];terms.append(term)
            for j,s in enumerate(choice):
                for v,w in zip(term,traces[j]):
                    clauses.extend([[-s,-v,w],[-s,v,-w]])
        for a in range(i):clauses.extend([-sel[0][a],-sel[1][b]] for b in range(a))
        for a,b,y in zip(*terms,traces[i]):
            clauses.extend([[-op,-a,-b,y],[-op,a,-y],[-op,b,-y],[op,a,b,-y],[op,-a,y],[op,-b,y]])
        selectors.append((op,sel))
    clauses.extend([v if m>>i&1 else -v] for i,v in enumerate(traces[-1]))
    return nvars,clauses,selectors
def run(k,control=None):
 n,cs,sel=encode(k)
 if control:
  for (op,S),(kind,a,b) in zip(sel,control,strict=True):
   a,b=sorted((a,b));cs.extend([[op if kind=='and' else -op],[S[0][a]],[S[1][b]]])
 file=d/('control.cnf' if control else 'search.cnf')
 with file.open('w') as f:
  print('p cnf',n,len(cs),file=f)
  for c in cs:print(*c,0,file=f)
 log=file.with_suffix('.log')
 with log.open('w') as f:r=subprocess.run([solver,'-t',str(30 if control else 1200),file],stdout=f)
 if r.returncode==10:
  model={int(x) for line in log.read_text().splitlines() if line.startswith('v ') for x in line[2:].split()}
  gs=[('and' if op in model else 'or',*[next(i for i,v in enumerate(opts) if v in model) for opts in S]) for op,S in sel]
  for i,row in enumerate(rows):
   x=[row>>j&1 for j in range(16)]
   for op,a,b in gs:x.append(x[a]&x[b] if op=='and' else x[a]|x[b])
   assert x[-1]==m>>i&1
  if not control:(d/'witness.json').write_text(json.dumps(gs))
 return r.returncode
if __name__=='__main__':
 lock=(d/'solver.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 ref=json.loads((d/'boxes.json').read_text());assert run(len(ref),ref)==10
 print('control passed',flush=True)
 result=run(24);(d/'outcome').write_text({0:'UNKNOWN',10:'SAT',20:'UNSAT'}.get(result,'ERROR'))
