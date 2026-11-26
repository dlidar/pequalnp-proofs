"""Independent lower certificate for every recorded conditional cover.

For each representative, construct the family of violated-axiom sets from
individual assignments. Enumerate candidate axiom sets one smaller than the
reported optimum, with all singleton-forced keys already selected.
"""
import json
from itertools import combinations
from pathlib import Path
def bad_set(x):
 result={i for i in range(4) if all(not (x>>(3*i+h)&1) for h in range(3))}
 pairs=list(combinations(range(4),2))
 result.update(4+6*h+k for h in range(3) for k,(i,j) in enumerate(pairs) if all(x>>(3*u+h)&1 for u in (i,j)))
 return frozenset(result)
def check():
 d=Path(__file__).parent
 rows=[bad_set(i) for i in range(4096)]
 for m,(weight,low,high,a,b) in json.loads((d/'roots.json').read_text()).items():
  for side,mask,size in [(0,low,a),(1,high,b)]:
   sets={z for x,z in enumerate(rows) if (x&int(m)).bit_count()%2==side}
   witness={i for i in range(22) if mask>>i&1}
   assert len(witness)==size and all(z&witness for z in sets)
   must={next(iter(z)) for z in sets if len(z)==1}
   budget=size-1-len(must)
   if budget<0:continue
   rem=sorted((z for z in sets if not z&must),key=len)
   small=[]
   for z in rem:
    if not any(y<=z for y in small):small.append(z)
   assert all(any(z.isdisjoint(extra) for z in small)
              for extra in combinations(set(range(22))-must,budget))
 print('172 optimum values verified by enumerating smaller axiom sets.')
if __name__=='__main__':check()
