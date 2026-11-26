"""Axiom support required on each side of a parity pivot, PHP(4,3)."""
from itertools import combinations, permutations
from functools import lru_cache
from pathlib import Path
import json
from collections import Counter
univ=(1<<4096)-1
raw=[sum(1<<x for x in range(4096) if x>>i&1) for i in range(12)]
par=[0]
for t in raw:par += [p^t for p in par]
edges=[(3*i+h,3*j+h) for h in range(3) for i,j in combinations(range(4),2)]
bad=[univ^(raw[3*i]|raw[3*i+1]|raw[3*i+2]) for i in range(4)]+[raw[i]&raw[j] for i,j in edges]
labels=[sum(1<<i for i,z in enumerate(bad) if z>>x&1) for x in range(4096)]
unique=[sum(1<<x for x,l in enumerate(labels) if l==1<<i) for i in range(22)]
def cover(dom):
 chosen=0
 rem=dom
 for i,p in enumerate(unique):
  if p & dom:chosen |= 1<<i; rem &=~bad[i]
 if rem==0:return chosen
 @lru_cache(None)
 def aux(r):
  if not r:return 0
  opts=(1<<22)-1
  s=r
  while s:
   b=s&-s;l=labels[b.bit_length()-1];s^=b
   if l.bit_count()<opts.bit_count():opts=l
   if opts.bit_count()==2:break
  best=None
  while opts:
   i=opts&-opts;opts^=i
   a=i|aux(r&~bad[i.bit_length()-1])
   if best is None or a.bit_count()<best.bit_count():best=a
  return best
 return chosen|aux(rem)
def group():
 for a in permutations(range(4)):
  for b in permutations(range(3)):
   yield [1<<(3*a[i//3]+b[i%3]) for i in range(12)]
def orbit(mask):
 return {sum(v for i,v in enumerate(p) if mask>>i&1) for p in group()}
def main():
 results={}; todo=set(range(1,4096))
 while todo:
  m=min(todo);o=orbit(m);todo-=o
  lo=cover(univ^par[m]);hi=cover(par[m]); z=(lo.bit_count(),hi.bit_count())
  results[m]=[len(o),lo,hi,*z]
 assert sum(r[0] for r in results.values())==4095
 hist=Counter()
 for m,(n,l,h,a,b) in results.items():hist[a+b]+=n
 print(len(results),sorted(hist.items()),flush=True)
 print('min',[(m,v) for m,v in results.items() if sum(v[-2:])==min(hist)],flush=True)
 Path('work/120/roots.json').write_text(json.dumps(results))
if __name__=='__main__':main()
