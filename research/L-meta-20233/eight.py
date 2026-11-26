"""Test four disjoint four-label blocks, with two arbitrary monotone signals per block."""
from pathlib import Path
import itertools,json
from functools import lru_cache
d=Path(__file__).parent;m=14466700110149527140
raw=[1<<(k//8)|1<<(8+k%8) for k in range(64)]
pn=[(p,n) for p in range(64) if m>>p&1 for n in range(64) if not(m>>n&1)]
states=tuple(u|v for u in (0,1,2) for v in (0,4,8))
mono=[a for a in range(512) if all(not (a>>i&1) or (a>>j&1) or (s&~t) for i,s in enumerate(states) for j,t in enumerate(states))]
tables=[(a,b) for a,b in itertools.combinations(mono,2)]
viable={s for s,_ in json.loads((d/'two-bits.json').read_text())['4']['possible']}
sets={i:sorted(s for s in viable if s>>i&1) for i in range(16)}
opts={}
for s in viable:
 sub=[i for i in range(16) if s>>i&1]
 ids=[states.index(sum(1<<j for j,k in enumerate(sub) if x>>k&1)) for x in raw]
 pairs=sorted(set((ids[p],ids[n]) for p,n in pn))
 req=sorted(set((ids[p],ids[n]) for p,n in pn if not raw[p]&~(raw[n]|s)))
 def sep(a,x,y):return (a>>x&1) and not(a>>y&1)
 classes={}
 for a,b in tables:
  if not all(sep(a,x,y) or sep(b,x,y) for x,y in req):continue
  signature=sum(1<<k for k,(x,y) in enumerate(pairs) if sep(a,x,y) or sep(b,x,y))
  classes.setdefault(signature,(a,b))
 # More separations can only help a monotone decoder; keep inclusion-maximal patterns.
 opts[s]=[]
 for sig,(a,b) in classes.items():
  if any(sig!=t and not(sig&~t) for t in classes):continue
  sepbits=sum(1<<k for k,(p,n) in enumerate(pn) if sep(a,ids[p],ids[n]) or sep(b,ids[p],ids[n]))
  opts[s].append((sepbits,a,b))
top=(1<<len(pn))-1
@lru_cache(None)
def separators(rem):
 return sum(1<<k for k,(p,n) in enumerate(pn) if raw[p]&~raw[n]&rem)
valid=[]
def cover(rem,done,seq):
 if not rem:
  if done==top:valid.append(seq)
  return
 j=(rem&-rem).bit_length()-1
 for s in sets[j]:
  if s&rem!=s:continue
  nxt=rem^s
  for bits,a,b in opts[s]:
   upd=done|bits
   if upd|separators(nxt)==top:cover(nxt,upd,seq+[(s,a,b)])
cover(65535,0,[])
print('viable subsets',len(viable),'nondominated encoder choices',sum(map(len,opts.values())),'eight-signal solutions after pruning',len(valid),flush=True)
if valid:(d/'eight-code.json').write_text(json.dumps(valid))
