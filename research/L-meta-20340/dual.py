from pathlib import Path
from fractions import Fraction
from itertools import combinations
from math import lcm
import numpy as np,json
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
m=1885146376704737940
P=[p for p in range(64) if m>>p&1];N=[n for n in range(64) if not m>>n&1]
def on(i,x):return i in (x//8,8+x%8)
def rects():
 for i in range(16):
  I=[a for a,p in enumerate(P) if on(i,p)];J=[b for b,n in enumerate(N) if not on(i,n)]
  for k in range(1,len(I)+1):
   for T in combinations(I,k):yield T,J
base=len(P)*len(N);nxt=base;cs=[];rhs=[]
for T,J in rects():
 extra=[]
 for j in J:
  cs.append({**{a*len(N)+j:1 for a in T},nxt:-1});rhs.append(0);extra.append(nxt);nxt+=1
 cs.append(dict.fromkeys(extra,1));rhs.append(1)
triples=[(i,j,v) for i,row in enumerate(cs) for j,v in row.items()]
i,j,v=zip(*triples)
A=coo_matrix((v,(i,j)),shape=(len(cs),nxt)).tocsr()
res=linprog(np.r_[-np.ones(base),np.zeros(nxt-base)],A_ub=A,b_ub=rhs,bounds=[(-5,1)]*base+[(0,None)]*(nxt-base),method='highs')
assert res.success
for denom in [1,2,4,8,16,32,64,128,256,512,1024,10000]:
 w=np.rint(res.x[:base]*denom).astype(int).reshape((len(P),len(N)))
 mx=max(sum(max(0,sum(w[i,j] for i in T)) for j in J) for T,J in rects())
 if (w.sum()+mx-1)//mx==int(np.ceil(-res.fun-0.000001)):break
print('total',w.sum(),'maximum',mx,'LP',-res.fun,flush=True)
Path(__file__).with_name('weight.json').write_text(json.dumps({'total':int(w.sum()),'maximum':int(mx),'weights':w.tolist()}))
