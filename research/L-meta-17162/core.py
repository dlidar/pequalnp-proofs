"""Enumerate four-row minimum-degree-two incidence cores and gate-elimination bounds."""
from functools import lru_cache
from itertools import combinations,permutations
from collections import Counter
import json
blocks=[x for x in range(1,16) if x.bit_count()>=2]
def valid(cols):
 return all(sum(v>>i&1 for v in cols)>=2 for i in range(4)) and all((v&w).bit_count()<=1 for v,w in combinations(cols,2))
def canon(cols):
 return min(tuple(sorted(sum(1<<p[i] for i in range(4) if v>>i&1) for v in cols)) for p in permutations(range(4)))
def graphs():
 families=[tuple(v for i,v in enumerate(blocks) if s>>i&1) for s in range(1<<len(blocks))]
 return Counter(canon(cols) for cols in families if valid(cols))
def elim(cols):
 n=4+len(cols)
 edges=[(i,4+j) for j,v in enumerate(cols) for i in range(4) if v>>i&1]
 @lru_cache(None)
 def bound(positive,negative):
  w=[i for i in range(n) if not (positive|negative)>>i&1]
  pos=[i for i in range(n) if positive>>i&1]
  if any(a in pos and b in pos for a,b in edges):return -1
  singles={b for a,b in edges if a in pos and b in w}|{a for a,b in edges if b in pos and a in w}
  residual=[(a,b) for a,b in edges if a in w and b in w and a not in singles and b not in singles]
  active=sorted(singles|{u for e in residual for u in e})
  if not active:return -1
  if len(active)==1:return 0
  if not residual:return len(active)-1
  cofs={i:(bound(positive,negative|1<<i),bound(positive|1<<i,negative)) for i in active}
  root=[]
  for i,j in combinations(active,2):
   for annihilator in [0,1]:
    v=len(active)-1
    for k,(b0,b1) in cofs.items():
     for s,h in enumerate([b0,b1]):
      if h>=0:v=max(v,h+1+int(k in (i,j) and s==annihilator))
    root.append(v)
  return min(root)
 b=bound(0,0)
 return dict(columns=cols,edges=len(edges),gate_elimination=b,star_upper=len(edges)+3)
if __name__=='__main__':print(json.dumps([dict(orbit=o,**elim(s)) for s,o in graphs().items()],indent=2))
