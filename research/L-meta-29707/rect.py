from pathlib import Path
from itertools import product
from functools import lru_cache
import json
from upper import edges,target
p=Path(__file__).resolve().parent
emap={e:1<<j for j,e in enumerate(edges)}
rect=[]
for c in product(range(3),repeat=8):
 L=[i for i,v in enumerate(c) if v==1];R=[i for i,v in enumerate(c) if v==2]
 if not L or not R or min(L)>min(R):continue
 E={tuple(sorted((i,j))) for i in L for j in R}
 if E<=emap.keys():rect.append((sum(emap[e] for e in E),sum(1<<i for i in L),sum(1<<i for i in R)))
def raw(x):return x&(x-1)==0
@lru_cache(None)
def build(req):
 if not req:return ()
 S=max(req,key=lambda s:(s.bit_count(),s))
 new=set(req)-{S};best=None
 # All proper-subset operands whose union is S, overlap permitted.
 subs=[i for i in range(1,S) if not i&~S]
 for i,a in enumerate(subs):
    for b in subs[i+1:]:
        if a|b!=S:continue
        ns=new|{v for v in (a,b) if not raw(v)}
        if best and len(ns)+1>=len(best):continue
        steps=build(tuple(sorted(ns)))+((a,b),)
        if best is None or len(steps)<len(best):best=steps
 return best
def circuit(cov,ors):
 gs=[];wires={1<<i:i for i in range(8)}
 def op(k,a,b):gs.append((k,a,b));return 8+len(gs)-1
 for a,b in ors:wires[a|b]=op('or',wires[a],wires[b])
 y=[op('and',wires[a],wires[b]) for _,a,b in cov];out=y[0]
 for b in y[1:]:out=op('or',out,b)
 assert all(evalg(gs,x)==target(x) for x in range(256))
 return gs
def evalg(gs,x):
 w=[bool(x>>i&1) for i in range(8)]
 for op,a,b in gs:w.append((w[a]&w[b]) if op=='and' else (w[a]|w[b]))
 return w[-1]
def main():
 best=15;full=(1<<len(edges))-1;seen=set();witness=None
 def search(mask,ids,required):
    nonlocal best,witness
    if ids in seen:return
    seen.add(ids)
    lower=len(required)+2*len(ids)-1
    if lower>=best:return
    if mask==full:
        ors=build(tuple(sorted(required)))
        cost=len(ors)+2*len(ids)-1
        if cost<best:
            best=cost;witness=circuit([rect[i] for i in ids],ors)
            print('upper',best,flush=True)
        return
    if lower+2>=best:return
    e=(~mask)&(mask+1)
    for i,(E,a,b) in enumerate(rect):
        if E&e:search(mask|E,tuple(sorted((*ids,i))),required|{v for v in (a,b) if not raw(v)})
 search(0,(),set())
 print('optimum',best,'families',len(seen),'products',len(rect))
 (p/'rect.json').write_text(json.dumps({'upper':witness,'size':best,'families':len(seen)}))
if __name__=='__main__':main()
