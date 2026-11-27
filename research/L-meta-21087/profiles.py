from itertools import combinations,product
from functools import lru_cache
from pathlib import Path
from collections import Counter
import json
d=Path(__file__).resolve().parent
M=114591
import sys
K=int(sys.argv[1])
n=4
pos=[i for i in range(20) if M>>i&1]
neg=[i for i in range(20) if not (M>>i&1)]
p=list(product(pos,neg))
width=len(p)
top=(1<<width)-1
one=top | (top<<width)
target=top<<width
def rawval(j,s):return j in (s//5,4+s%5)
raw=tuple(sum(int(rawval(j,z[0]) or 0)<<(i+width) | int(rawval(j,z[1]))<<i for i,z in enumerate(p)) for j in range(9))
@lru_cache(maxsize=160000)
def sep(x,t):return ((x>>width)^x)&top if t else (x>>width)&(~x)&top
def cuts(ws,t):
 m=0
 for x in ws:m|=sep(x,bool(t))
 return m==top
def children(k,t,ws):
 extra=k+1-len(ws)-t
 if t:
  for i,a in enumerate(ws):
   z=one^a
   if z in (0,one) or z in ws:continue
   r=ws[:i]+ws[i+1:]
   for keep in [(),(a,)]:
    ch=(z,)+keep+r
    if len(keep)<=extra and cuts(ch,t-1):yield t-1,ch,('not',a,a,z)
 for i,j in combinations(range(len(ws)),2):
  a,b=ws[i],ws[j];r=ws[:i]+ws[i+1:j]+ws[j+1:]
  for op,z in [('and',a&b),('or',a|b)]:
   if z in (0,one) or z in ws:continue
   for keep in [(),(a,),(b,),(a,b)]:
    ch=(z,)+keep+r
    if len(keep)<=extra and cuts(ch,t):yield t,ch,(op,a,b,z)
def roots():
 return [(t,ws) for t in range(K+2) for j in range(1,min(K+1-t,len(raw))+1) for ws in combinations(raw,j) if cuts(ws,t)]
@lru_cache(maxsize=100000)
def solve(k,t,ws):
 if not t and ws==(target,):return ()
 if not k:return
 for u,ch,g in children(k,t,ws):
  path=solve(k-1,u,tuple(sorted(ch)))
  if path is not None:return (g,)+path

if __name__=='__main__':
 results=[]
 for t,ws in roots():
    path=solve(K,t,tuple(sorted(ws)))
    if path is None:continue
    stock=list(raw);gates=[]
    for op,a,b,v in path:
        gates.append([op,[stock.index(a)] if op=='not' else [stock.index(a),stock.index(b)]])
        stock.append(v)
    assert len(gates)==8 and sum(op=='not' for op,ins in gates)==t
    used={i for op,ins in gates for i in ins if i<9}
    assert sorted(used)==[raw.index(x) for x in ws]
    for i in range(20):
        wires=[j in (i//5,4+i%5) for j in range(9)]
        for op,ins in gates:
            b=[wires[j] for j in ins]
            wires.append(not b[0] if op=='not' else (all(b) if op=='and' else any(b)))
        assert wires[stock.index(target)]==bool(M>>i&1)
    results.append(dict(inverters=t,inputs=sorted(used),gates=gates))
 (d/'profiles.json').write_text(json.dumps(results,indent=1))
 print('roots',len(roots()),'realized',[(r['inverters'],r['inputs']) for r in results])
