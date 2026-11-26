"""Exhaustively classify two monotone bit encoders on three or four raw labels."""
import itertools,json
from pathlib import Path
d=Path(__file__).parent
m=14466700110149527140
raw=[(1<<(i//8))|(1<<(8+i%8)) for i in range(64)]
posit=[i for i in range(64) if m>>i&1];neg=[i for i in range(64) if not m>>i&1]
def tables(n):
 t=[0,1]
 for i in range(n):
  t=[a|(b<<(1<<i)) for a in t for b in t if a&~b==0]
 return t
def check(size):
 mono=tables(size);assert len(mono)=={3:20,4:168}[size]
 possible=[];nonpartition=[];counts={};patterns={}
 for sub in itertools.combinations(range(16),size):
  s=sum(1<<i for i in sub)
  compact=[sum(1<<j for j,i in enumerate(sub) if x>>i&1) for x in raw]
  # Only ordered complementary observations impose a separation clause.
  req=tuple(sorted({(compact[p],compact[n]) for p in posit for n in neg if raw[p]&~(raw[n]|s)==0}))
  if req in patterns:solution,disjoint=patterns[req]
  else:
   goal=(1<<len(req))-1
   sig={};supports={}
   for t in mono:
    hit=sum(1<<j for j,(p,n) in enumerate(req) if t>>p&1 and not(t>>n&1))
    deps=sum(1<<j for j in range(size) if any((t>>k^t>>(k^(1<<j)))&1 for k in range(1<<size)))
    sig.setdefault(hit,[]).append(t);supports[t]=deps
   solution=disjoint=None
   for x,f in sig.items():
    for y,g in sig.items():
     if (x|y)!=goal:continue
     if solution is None:solution=(f[0],g[0])
     for i,j in itertools.product(f,g):
      if not supports[i]&supports[j]:disjoint=(i,j);break
     if disjoint:break
    if disjoint:break
   patterns[req]=(solution,disjoint)
  if solution is not None:
   possible.append([s,solution])
   counts[sum(i<8 for i in sub)]=counts.get(sum(i<8 for i in sub),0)+1
   if disjoint is None:nonpartition.append(s)
 print('size',size,'viable',len(possible),'overlap required',len(nonpartition),'row counts',counts,'patterns',len(patterns),flush=True)
 return {'possible':possible,'overlap_required':nonpartition}
result={k:check(k) for k in (3,4)}
(d/'two-bits.json').write_text(json.dumps(result))
