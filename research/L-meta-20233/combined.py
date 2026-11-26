"""Combine one four-label two-bit code with mutually disjoint ORs on other labels."""
import itertools,json
from pathlib import Path
from collections import Counter
d=Path(__file__).parent;m=14466700110149527140
raw=[1<<(k//8)|1<<(8+k%8) for k in range(64)]
ps=[k for k in range(64) if m>>k&1];ns=[k for k in range(64) if not m>>k&1]
local=[a|b for a in (0,1,2) for b in (0,4,8)]
best=17;examples=[];records=[]
for s,[(price,a,b,gates)] in json.loads((d/'four-encoders.json').read_text()):
 v=[i for i in range(16) if s>>i&1]
 indices=[local.index(sum(1<<j for j,x in enumerate(v) if t>>x&1)) for t in raw]
 bits=[((a>>i)&1)<<16 | ((b>>i)&1)<<17 for i in indices]
 pairs=[(i,j) for i in range(8) for j in range(8) if not(s&(1<<i|1<<(8+j))) and not(m>>(8*i+j)&1)]
 # A row/column OR can only remove separations. Store per-pair forbidden sets of removed labels.
 needed=[(raw[p]&~(raw[n]|s),raw[n]) for p in ps for n in ns if not bits[p]&~bits[n]]
 def extend(k,used,merged,cuts):
  global best,examples
  width=14-len(merged)
  if width<best:best=width;examples=[]
  if width==best:examples.append([s,merged])
  for h in range(k,len(pairs)):
   i,j=pairs[h];t=1<<i | 1<<(j+8)
   if t&used:continue
   # When the negative already has one of these coordinates, separation provided by either endpoint is lost.
   nxt=[(z&~t if neg&t else z,neg) for z,neg in cuts]
   if all(z for z,neg in nxt):extend(h+1,used|t,merged+[(i,j)],nxt)
 extend(0,s,[],needed)
print('minimum for the 81 saved codes and disjoint additional ORs',best,'attaining choices',len(examples),examples[:1])
for s,merged in examples:
 a,b=next(entry[1][0][1:3] for entry in json.loads((d/'four-encoders.json').read_text()) if entry[0]==s)
 v=[i for i in range(16) if s>>i&1];codes=[]
 for t in raw:
  i=local.index(sum(1<<k for k,x in enumerate(v) if t>>x&1))
  z=t&~s|((a>>i)&1)<<16|((b>>i)&1)<<17
  for r,c in merged:
   mask=1<<r|1<<(c+8)
   z=(z&~mask)|(int(bool(z&mask))<<r)
  codes.append(z)
 assert all(codes[p]&~codes[n] for p in ps for n in ns)
(d/'combined.json').write_text(json.dumps({'width':best,'choices':examples}))
