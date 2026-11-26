"""Enumerate all two-gate bypasses of the 60-gate point-star reference, preserving the first gate. Each output can be renamed independently. The objective counts incorrect labeled output/test pairs."""
from itertools import combinations
P=[i for i in range(13) if i!=9]
edges=[(i,j) for i,a in enumerate(P) for j,b in enumerate(range(1,13),12) if (a+b)%13 in (0,1,3,9)]
A=sum(1<<k for k in [0,1,3]);B=sum(1<<k for k in [15,16,18]);allbits=2**24-1
def boundary(remove):
 allow=allbits^remove
 left=allow&4095;right=allow>>12
 neighbors=[sum(1<<(j-12) for a,j in edges if a==i) for i in range(12)]
 out=set()
 for s in range(4096):
  if s & ~left:continue
  t=right
  for i,n in enumerate(neighbors):
   if s>>i&1:t&=~n
  if any((left&~s)>>i&1 and not(t&n) for i,n in enumerate(neighbors)):continue
  out.add(s|(t<<12))
 return out

def tests():
 req={}
 def setv(x,t,v):
  a=req.setdefault(x,[None]*3);assert a[t] in (None,v);a[t]=v
 for i,j in edges:setv((1<<i)|(1<<j),0,True)
 for t,d in enumerate([0,A,B]):
  for x in boundary(d):setv(x,t,False)
  if t:
   for i in range(24):
    if d>>i&1:setv(1<<i,t,True)
 return req
def reference():
 g=[]
 def add(op,i,j):g.append((op,i,j));return 23+len(g)
 a=add(False,0,1);a=add(False,a,3)
 b=add(False,15,16);b=add(False,b,18)
 roots=[]
 for i in range(12):
  js=[j for p,j in edges if p==i];r=js[0]
  for t in js[1:]:r=add(False,r,t)
  roots.append(add(True,i,r))
 r=roots[0]
 for t in roots[1:]:r=add(False,r,t)
 return g,[r,a,b]
def vals(g,o,x):
 v=[bool(x>>i&1) for i in range(24)]
 for op,a,b in g:v.append((v[a] and v[b]) if op else (v[a] or v[b]))
 return [v[i] for i in o]
def correct(g,o,req):
 return all(all(a is None or a==b for a,b in zip(y,vals(g,o,x))) for x,y in req.items())

from itertools import combinations,product
from pathlib import Path
import json
req=tests(); rows=sorted(req); g,outputs=reference()
ones=[sum(1<<k for k,x in enumerate(rows) if req[x][i] is True) for i in range(3)]
zeros=[sum(1<<k for k,x in enumerate(rows) if req[x][i] is False) for i in range(3)]
raw=[sum(1<<k for k,x in enumerate(rows) if x>>i&1) for i in range(24)]
best=999; ties=0;count=0
for (i,j),(a,b) in product(combinations(range(1,len(g)),2),product((1,2),repeat=2)):
 vals=raw.copy();ind=list(range(24));gs=[]
 for k,(op,u,v) in enumerate(g):
  if k==i or k==j:
   ind.append(ind[g[k][a if k==i else b]])
   continue
  x,y=ind[u],ind[v];ind.append(len(vals));gs.append((op,x,y))
  vals.append((vals[x]&vals[y]) if op else (vals[x]|vals[y]))
 picks=[];err=[]
 for t in range(3):
  ms=[(ones[t]&~z)|(zeros[t]&z) for z in vals]
  h=min(range(len(vals)),key=lambda idx:ms[idx].bit_count());picks.append(h);err.append(ms[h])
 score=sum(z.bit_count() for z in err);count+=1
 if score<best:
  best=score;ties=0
  failures=[(rows[k],t) for t in range(3) for k in range(len(rows)) if err[t]>>k&1]
  witness=dict(gates=gs,outputs=picks,tagged_failures=failures,deleted=[i,j],operand=[a,b])
 if score==best:ties+=1
print('two-gate bypasses',count,'minimum tagged failures',best,'tied constructions',ties,'example',witness['tagged_failures'])
assert len(witness['gates'])==58
if best==0:assert correct(witness['gates'],witness['outputs'],req)
(Path(__file__).parent/'nearest.json').write_text(json.dumps(witness))
