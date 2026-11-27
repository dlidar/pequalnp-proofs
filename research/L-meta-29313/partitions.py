"""Decide whether 14 monochromatic leaf rectangles can partition the promise matrix."""
from functools import lru_cache
from pathlib import Path
import json,time
p=Path(__file__).resolve().parent
data=json.loads((p/'mono-weights.json').read_text())
P,N,w,cap=[data[k] for k in ['P','N','weights','cap']]
r,c=len(P),len(N)
score=sum(map(sum,w))
boxes={}
def subs(mask):
 t=mask
 while t:
  yield t;t=(t-1)&mask
for i in range(8):
 rows=sum(1<<j for j,x in enumerate(P) if x>>i&1)
 cols=sum(1<<j for j,x in enumerate(N) if not x>>i&1)
 for a in subs(rows):
  for b in subs(cols):
   rect=sum(b<<(c*j) for j in range(r) if a>>j&1)
   if rect in boxes:continue
   mass=sum(w[j][k] for j in range(r) if a>>j&1 for k in range(c) if b>>k&1)
   assert mass<=cap
   if mass>0:boxes[rect]=cap-mass
cells=[[ (rect,d) for rect,d in boxes.items() if rect>>i&1] for i in range(r*c)]
for row in cells:row.sort(key=lambda x:(x[1],-x[0].bit_count()))
nodes=0
@lru_cache(None)
def go(remaining,k,slack):
 global nodes
 nodes+=1
 if not remaining:return () if k==0 else None
 if k==0:return None
 best=None
 for i in range(r*c):
  if not (remaining>>i&1):continue
  hit=[(box,d) for box,d in cells[i] if d<=slack and box&remaining==box]
  if not hit:return None
  if best is None or len(hit)<len(best):best=hit
 for box,d in best:
  ans=go(remaining^box,k-1,slack-d)
  if ans is not None:return (box,)+ans
 return None
if __name__=='__main__':
 ans=go((1<<(r*c))-1,14,14*cap-score)
 print('eligible boxes',len(boxes),'nodes',nodes,'solution',ans,flush=True)
 if ans:(p/'partition14.json').write_text(json.dumps(ans))
