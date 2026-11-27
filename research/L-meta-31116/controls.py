from pathlib import Path
import json,subprocess
from upper import target
p=Path(__file__).resolve().parent
g=json.loads((p/'upper.json').read_text())['gates']
w=[]
for x in range(256):
 v=[(x>>i)&1 for i in range(8)]
 for op,a,b in g:v.append(v[a]&v[b] if op=='and' else v[a]|v[b])
 assert bool(v[-1])==target(x)
 w.append(v)
# Supply the first eleven signals derived from gates and the raw inputs.
# The final three ORs combine four products. The witness and all states are re-evaluated.
c=json.loads((p/'census.json').read_text());rows=c['positive']+c['negative']
sig=[sum(w[x][i]<<j for j,x in enumerate(rows)) for i in range(8+len(g)-3)]
# Include only the four inputs of this particular tail, to make exhaustive controls tiny.
idx=[10,14,17,18];ls=[sig[i] for i in idx]
(p/'control.task').write_text('14 6 4\n'+' '.join(map(str,ls))+'\n')
for exe in ['fast','frontier']:
 for k,verdict in [(2,'UNSAT'),(3,'SAT')]:
  ans=subprocess.check_output([str(p/exe),str(p/'control.task'),str(k)],text=True)
  assert ans.split()[0]==verdict,(k,ans)
  if verdict=='SAT':
   tables={lab:[w[x][i] for x in range(256)] for lab,i in zip(ls,idx)}
   for line in ans.splitlines()[1:]:
    op,a,b,z=line.split();a,b,z=map(int,[a,b,z]);tables[z]=[(s&t if op=='a' else s|t) for s,t in zip(tables[a],tables[b])]
   assert tables[(1<<14)-1]==[int(target(x)) for x in range(256)]
  print(exe,k,verdict)
