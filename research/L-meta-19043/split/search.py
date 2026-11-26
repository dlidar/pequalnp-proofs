from itertools import combinations,product
from functools import lru_cache
from pathlib import Path
from collections import Counter
import json
d=Path(__file__).resolve().parent
M=5805
K=9
n=4
pos=[i for i in range(n*n) if M>>i&1]
neg=[i for i in range(n*n) if not (M>>i&1)]
p=list(product(pos,neg))
width=len(p)
top=(1<<width)-1
one=top | (top<<width)
target=top<<width
def rawval(j,s):return j in (s//n,n+s%n)
raw=tuple(sum(int(rawval(j,z[0]) or 0)<<(i+width) | int(rawval(j,z[1]))<<i for i,z in enumerate(p)) for j in range(2*n))
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
 rs=roots()
 print('viable roots',Counter((t,len(ws)) for t,ws in rs),flush=True)
 for i,(t,ws) in enumerate(rs):
  pth=solve(K,t,tuple(sorted(ws)))
  if pth is not None:
   stock=list(raw);gs=[]
   for op,a,b,v in pth:gs.append([op,[stock.index(a)] if op=='not' else [stock.index(a),stock.index(b)]]);stock.append(v)
   (d/'witness.json').write_text(json.dumps([gs,stock.index(target)]));print('candidate',i,flush=True);break
  print(i,t,len(ws),'no path',flush=True)
 else:print('all roots found false by independent search',flush=True);(d/'no-path').touch()
