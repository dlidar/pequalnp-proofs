"""Rebuild maximal boxes from all row subsets and verify integer dual bounds."""
from pathlib import Path
from itertools import product
from array import array
import json
import numpy as np
D=Path(__file__).resolve().parent
N=21; FULL=(1<<21)-1; BASE=1179809
rows=[((BASE<<i)|(BASE>>(21-i)))&FULL for i in range(21)]
def independent_boxes():
 allowed=array('I',[FULL])*(1<<21)
 for s in range(1,1<<21):
  b=s&-s;allowed[s]=allowed[s^b]&~rows[b.bit_length()-1]
 cs=set(allowed);cs.discard(0);cs.discard(FULL)
 return [(sum(1<<i for i,row in enumerate(rows) if not row&b),b) for b in sorted(cs)]
def main():
 bs=independent_boxes();assert len(bs)==25235
 cells=[(i,j) for i,j in product(range(3),range(21)) if not rows[i]>>j&1]
 index={( (i+s)%21,(j+s)%21):k for k,(i,j) in enumerate(cells) for s in range(0,21,3)}
 counts=np.zeros((len(bs),48),dtype=np.int16)
 for k,(a,b) in enumerate(bs):
  for i in range(21):
   if not a>>i&1:continue
   for j in range(21):
    if b>>j&1:counts[k,index[i,j]]+=1
 footprints={sum(1<<i for i,v in enumerate(row) if v) for row in counts}
 assert len(footprints)==3514
 perms=set()
 for u in range(21):
  if len({(u*i)%21 for i in range(21)})!=21:continue
  for v in range(21):
   for w in range(21):
    if all(((rows[0]>>j)&1)==((rows[v]>>((u*j+w)%21))&1) for j in range(21)):
     if not all((rows[i]>>j&1)==(rows[(u*i+v)%21]>>((u*j+w)%21)&1) for i in range(21) for j in range(21)):continue
     perms.add(tuple(index[(u*i+v)%21,(u*j+w)%21] for i,j in cells))
 hit=set();exc=set();certs=json.loads((D/'all-residual-duals.json').read_text())
 for m,num,w,cap,total in certs:
  js=[j for j in range(48) if not (m>>j)&1]
  assert len(w)==len(js) and min(w)>=0 and total==7*sum(w)
  actual=int((counts[:,js].T.astype(np.int64).T@np.array(w,dtype=np.int64)).max())
  assert actual<=cap and total>7*cap
  orbit={sum(1<<p[j] for j in range(48) if m>>j&1) for p in perms}
  assert len(orbit)==num and not hit&orbit
  hit|=orbit
  if total<=8*cap:exc.update(orbit)
 assert hit==footprints and len(exc)==6
 print('Verified all 222 duals against 25235 full rectangles;',len(hit),'distinct footprints;',len(exc),'require the residual eight-box check.')
if __name__=='__main__':main()
