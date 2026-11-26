"""Enumerate all small joint encoders on local row/column promise states."""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import json,itertools
d=Path(__file__).parent; m=14466700110149527140
inputs=[(1<<(i//8))|(1<<(8+i%8)) for i in range(64)]
pos=[i for i in range(64) if m>>i&1];neg=[i for i in range(64) if not m>>i&1]
@lru_cache(None)
def mincost(args,req):
 raw=tuple(sum(1<<i for i,x in enumerate(args) if x>>j&1) for j in range(3))
 full=(1<<len(req))-1
 def sep(t):return sum(1<<i for i,(a,b) in enumerate(req) if t>>a&1 and not(t>>b&1))
 front={tuple(sorted(raw))}
 for k in range(5):
  nxt=set()
  for state in front:
   for a,b in itertools.combinations(state,2):
    if sep(a)|sep(b)==full:return k
    for t in (a&b,a|b):
     if t not in state:nxt.add(tuple(sorted((*state,t))))
  front=nxt
 raise ValueError('out of search range')
res=Counter();counts={}
for s,_ in json.loads((d/'two-bits.json').read_text())['3']['possible']:
 subset=[i for i in range(16) if s>>i&1]
 proj=[sum(1<<h for h,i in enumerate(subset) if t>>i&1) for t in inputs]
 states=tuple(sorted(set(proj)))
 req=tuple(sorted({(states.index(proj[a]),states.index(proj[b])) for a in pos for b in neg if inputs[a]&~(inputs[b]|s)==0}))
 k=mincost(states,req);res[k]+=1;counts[s]=k
print(sorted(res.items()))
(d/'triple-costs.json').write_text(json.dumps(counts))
