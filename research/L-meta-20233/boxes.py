import itertools,json
from pathlib import Path
from scipy.optimize import milp,Bounds,LinearConstraint
import numpy as np
from scipy.sparse import lil_matrix
d=Path(__file__).parent
m=14466700110149527140
def sub(v):
 t=v
 while t:yield t;t=(t-1)&v
def ones(v):return [i for i in range(8) if v>>i&1]
rows=[m>>(8*i)&255 for i in range(8)]
boxes=[]
for a in range(1,256):
 b=255
 for i in ones(a):b &=rows[i]
 boxes.extend((a,t) for t in sub(b))
edges=[(i,j) for i in range(8) for j in ones(rows[i])]
groups=[(k,v) for k in (0,1) for v in sorted({b[k] for b in boxes if b[k].bit_count()>1})]
n=len(boxes);G=dict(zip(groups,range(n,n+len(groups))));N=n+len(G);C=[];lb=[]
def add(a,l):C.append(a);lb.append(l)
for i,j in edges:add({h:1 for h,(a,b) in enumerate(boxes) if i in ones(a) and j in ones(b)},1)
for h,box in enumerate(boxes):
 for k,v in enumerate(box):
  if (k,v) in G:add({h:-1,G[k,v]:1},0)
for (k,v),t in G.items():
 if v.bit_count()==3:add({t:-1,**{G[k,u]:1 for u in sub(v) if u.bit_count()==2}},0)
A=lil_matrix((len(C),N))
for i,row in enumerate(C):
 for j,x in row.items():A[i,j]=x
res=milp(np.r_[[2]*n,[1]*len(G)],integrality=np.ones(N),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsr(),lb,np.inf))
selected=[box for h,box in enumerate(boxes) if res.x[h]>0.5]
print('boxes',n,'min',res.fun-1,'dual',res.mip_dual_bound-1,'selection',selected,flush=True)
gs=[];ws={(k,1<<i):k*8+i for k in [0,1] for i in range(8)}
def gate(op,a,b):gs.append((op,a,b));return 15+len(gs)
for k,v in sorted(groups,key=lambda kv:kv[1].bit_count()):
 if res.x[G[k,v]]<0.5:continue
 a=next(t for t in sub(v) if t.bit_count()==v.bit_count()-1 and (k,t) in ws)
 ws[k,v]=gate('or',ws[k,a],ws[k,v^a])
outs=[gate('and',ws[0,a],ws[1,b]) for a,b in selected]
o=outs[0]
for x in outs[1:]:o=gate('or',o,x)
assert len(gs)==round(res.fun)-1
(d/'boxes.json').write_text(json.dumps(gs))
