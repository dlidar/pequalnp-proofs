"""Verify the branching integer rectangle certificate and the paired-product construction."""
from pathlib import Path
import json
p=Path(__file__).resolve().parent
R=json.loads((p/'weights.json').read_text())['rows']
edges=[(i,j) for i in range(32) for j in range(32) if R[i]>>j&1]
allrows=(1<<32)-1
columns=[sum(1<<i for i,r in enumerate(R) if r>>j&1) for j in range(32)]
assert all(r!=allrows for r in R+columns)
S={allrows}
for c in columns:S.update(x&c for x in tuple(S))
boxes=sorted((x,sum(1<<j for j,c in enumerate(columns) if c&x==x)) for x in S if x and any(c&x==x for c in columns))
members=[{k for k,(u,v) in enumerate(edges) if r>>u&c>>v&1} for r,c in boxes]
import sys
goal=int(sys.argv[1]) if len(sys.argv)>1 else 29
import gzip
with gzip.open(p/f'cover-lower{goal}.json.gz','rt') as cert:nodes=json.load(cert)
cur=0
def visit(left,available,chosen):
 global cur
 n=nodes[cur];cur+=1
 if 'split' in n:
  k=n['split'];assert k in available
  rest=available-{k}
  visit(left-members[k],rest,chosen+1);visit(left,rest,chosen)
 else:
  w=dict(n['p']);assert len(w)==len(n['p']) and set(w)<=left and all(type(z)==int and z>0 for z in w.values())
  cap=max((sum(w.get(j,0) for j in members[i]) for i in available),default=0)
  assert sum(w.values())>(goal-1-chosen)*cap
visit(set(range(len(edges))),set(range(len(boxes))),0)
assert cur==len(nodes)
terms=json.loads((p/'products.json').read_text())
assert len(terms)==15
for u in range(32):
 for v in range(32):
  mask=1<<u|1<<(32+v)
  assert any(mask&a and mask&b for a,b in terms)==bool(R[u]>>v&1)
print(cur,'certificate nodes;',len(boxes),'maximal boxes; rectangle lower',goal,'; exact minimum mixed products',15)
