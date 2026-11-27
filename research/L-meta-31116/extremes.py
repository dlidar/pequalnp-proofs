"""Count small inverter inputs by boundary trace; retain optimal formula witnesses."""
import json
from pathlib import Path
d=Path(__file__).resolve().parent
data=json.loads((d/'census.json').read_text())
P,N=data['positive'],data['negative'];rows=P+N
raw=[sum((x>>i&1)<<j for j,x in enumerate(rows)) for i in range(8)]
levels=[{s:i for i,s in enumerate(raw)}];seen=set(raw)
for k in range(1,9):
 fresh={}
 for i in range((k-1)//2+1):
  for a in levels[i]:
   for b in levels[k-1-i]:
    for s,op in ((a&b,'and'),(a|b,'or')):
     if s not in seen and s not in fresh:fresh[s]=(op,levels[i][a],levels[k-1-i][b])
 levels.append(fresh);seen.update(fresh)
def compute(expr,x):
 if isinstance(expr,int):return (x>>expr)&1
 op,a,b=expr
 return compute(a,x)&compute(b,x) if op=='and' else compute(a,x)|compute(b,x)
out=[]
for s in data['worst_traces']:
 k=next(k for k,X in enumerate(levels) if s in X)
 expr=levels[k][s]
 assert all(compute(expr,x)==(s>>j&1) for j,x in enumerate(rows))
 positives=[x for j,x in enumerate(P) if not s>>j&1]
 negatives=[x for j,x in enumerate(N,len(P)) if s>>j&1]
 out.append(dict(trace=s,prefix_gates=k,prefix=expr,positive_tests=positives,negative_tests=negatives))
(d/'extremes.json').write_text(json.dumps(out,indent=2))
for r in out:
 if r['prefix_gates']==4:print(r)
