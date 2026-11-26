from pathlib import Path
from functools import lru_cache
import json,sys
d=Path(__file__).resolve().parent
rows=[1179809,262467,524934,1049868,2585,5170,10340,20680,41360,82720,165440,330880,661760,1323520,549889,1099778,102405,204810,409620,819240,1638480]
full=(1<<21)-1
def rot(m,k):return ((m<<k)|(m>>(21-k)))&full
def validate(rects):
 covered=[0]*21
 for a,b in rects:
  for i in range(21):
   if a>>i&1:
    assert not rows[i]&b;covered[i]|=b
 return sum(((full^row)&~c).bit_count() for row,c in zip(rows,covered))
def boxes():
 possible={full}
 for row in rows:possible.update(x&~row for x in tuple(possible))
 return sorted((sum(1<<i for i,row in enumerate(rows) if not row&b),b) for b in possible if b!=0 and b!=full)
def orbit(r,s):
 a,b=r
 return sorted(set((rot(a,h),rot(b,h)) for h in range(0,21,s)))
def quotient(s):
 bs=boxes(); reps=[r for r in bs if r==orbit(r,s)[0]]
 cells=[(i,j) for i in range(s) for j in range(21) if not rows[i]>>j&1]
 opts={}
 for r in reps:
  orb=orbit(r,s);mask=sum(1<<k for k,(i,j) in enumerate(cells) if any(a>>i&1 and b>>j&1 for a,b in orb))
  if mask and (mask not in opts or len(opts[mask])>len(orb)):opts[mask]=orb
 return cells,opts
if __name__=='__main__':
 from collections import Counter
 b=boxes()
 with (d/'boxes.txt').open('w') as f:
  for a,c in b:print(a,c,file=f)
 print('maximal',len(b),Counter((a.bit_count(),c.bit_count()) for a,c in b))
 for s in [1,3,7]:
  cells,opts=quotient(s)
  print('shift',s,len(cells),'orbit costs',Counter(map(len,opts.values())), 'max coverage by cost',{n:max(m.bit_count() for m,o in opts.items() if len(o)==n) for n in set(map(len,opts.values()))})
  (d/f'q{s}.json').write_text(json.dumps([[hex(m),o] for m,o in opts.items()]))
