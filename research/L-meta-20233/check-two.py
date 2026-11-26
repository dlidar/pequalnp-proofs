"""Cross-check two-bit classifications on the promise using all upward-closed local labelings."""
import json,itertools
from functools import lru_cache
from pathlib import Path
d=Path(__file__).parent;M=14466700110149527140
raw=[1<<(i//8)|1<<(8+i%8) for i in range(64)]
pos=[i for i in range(64) if M>>i&1];neg=[i for i in range(64) if not M>>i&1]
@lru_cache(None)
def local(states,mask):
 up=[]
 for sub in range(1<<len(states)):
  ok=True
  for i,x in enumerate(states):
   if not sub>>i&1:continue
   for j,y in enumerate(states):
    if (x&mask)&~(y&mask)==0 and not sub>>j&1:ok=False;break
   if not ok:break
  if ok:up.append(sub)
 return up
@lru_cache(None)
def exists(states,needed,a,b):
 options=[]
 for side in (a,b):
  opts=set()
  for bit in local(states,side):
   separated=sum(1<<k for k,(u,v) in enumerate(needed) if bit>>u&1 and not bit>>v&1)
   opts.add(separated)
  options.append(opts)
 goal=(1<<len(needed))-1
 return any(x|y==goal for x in options[0] for y in options[1])
data=json.loads((d/'two-bits.json').read_text())
for size in (3,4):
 reported={s for s,_ in data[str(size)]['possible']};over=set(data[str(size)]['overlap_required'])
 for subset in itertools.combinations(range(16),size):
  s=sum(1<<k for k in subset);full=(1<<size)-1
  projected=[sum(1<<h for h,k in enumerate(subset) if t>>k&1) for t in raw]
  states=tuple(sorted(set(projected)))
  needed=tuple(sorted({(states.index(projected[u]),states.index(projected[v])) for u in pos for v in neg if raw[u]&~(raw[v]|s)==0}))
  viable=exists(states,needed,full,full)
  assert viable==(s in reported)
  if viable:assert (s not in over)==any(exists(states,needed,a,full^a) for a in range(1<<size))
 print('all',size,'input subsets independently verified')
# Check each circuit used in the minimal overlapping encoders on all sixty-four cells.
support=[a|b for a in (0,1,2) for b in (0,4,8)]
raw_tables=[sum(1<<i for i,u in enumerate(support) if u>>j&1) for j in range(4)]
records=json.loads((d/'four-encoders.json').read_text())
for s,[(k,a,b,gs)] in records:
 subset=[i for i in range(16) if s>>i&1];codes=[]
 assert k==len(gs)
 for u in raw:
  signals={t:bool(u>>j&1) for t,j in zip(raw_tables,subset)}
  for op,p,q,t in gs:signals[t]=signals[p] and signals[q] if op=='and' else signals[p] or signals[q]
  codes.append((u&~s)|(int(signals[a])<<16)|(int(signals[b])<<17))
 assert all(codes[i]&~codes[j] for i in pos for j in neg)
print('all',len(records),'encoder circuits checked on every positive/negative pair')
