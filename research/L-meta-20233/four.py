from pathlib import Path
import itertools,json
from collections import Counter
d=Path(__file__).parent;m=14466700110149527140
M=json.loads((d/'two-bits.json').read_text())['4']
raw=[(1<<(i//8))|(1<<(8+i%8)) for i in range(64)]
p=[i for i in range(64) if m>>i&1];n=[i for i in range(64) if not m>>i&1]
# Work only on the nine possible local states of two row labels and two column labels.
local=[a|b for a in (0,1,2) for b in (0,4,8)]
rr=tuple(sum(1<<i for i,x in enumerate(local) if x>>k&1) for k in range(4))
def sig(A,req):
 return sum(1<<i for i,(x,y) in enumerate(req) if A>>x&1 and not(A>>y&1))
# Two wire output tables share the same circuit DAG.
cost={};front={tuple(sorted(rr)):[]}
for k in range(7):
 print('depth',k,'front',len(front),flush=True)
 nxt={}
 for state,gs in front.items():
  for a,b in itertools.combinations(state,2):cost.setdefault((a,b),(k,gs))
  if k==6:continue
  for a,b in itertools.combinations(state,2):
   for t,op in [(a&b,'and'),(a|b,'or')]:
    if t in state:continue
    s=tuple(sorted((*state,t)))
    if s not in nxt:nxt[s]=[*gs,(op,a,b,t)]
 front=nxt
res=[];cache={}
for s in M['overlap_required']:
 sub=[i for i in range(16) if s>>i&1]
 ix=[local.index(sum(1<<j for j,i in enumerate(sub) if row>>i&1)) for row in raw]
 req=tuple(sorted({(ix[i],ix[j]) for i in p for j in n if not raw[i]&~(raw[j]|s)}))
 if req not in cache:
  needed=(1<<len(req))-1;hit={a:sig(a,req) for ab in cost for a in ab}
  valid=sorted((k,a,b,gs) for (a,b),(k,gs) in cost.items() if hit[a]|hit[b]==needed)
  cache[req]=valid[:1]
 res.append((s,cache[req]))
print(Counter(v[0][0] if v else None for s,v in res),flush=True)
(d/'four-encoders.json').write_text(json.dumps(res))
