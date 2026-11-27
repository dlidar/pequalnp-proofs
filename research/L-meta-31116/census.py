"""Exact boundary repair prices for raw inverters and small monotone prefixes."""
import json,itertools
from pathlib import Path
from upper import edges,target
d=Path(__file__).resolve().parent
P=[1<<a|1<<b for a,b in edges]
N=[x for x in range(256) if not target(x) and all(target(x|1<<i) for i in range(8) if not x>>i&1)]
rows=P+N; allbits=(1<<len(rows))-1; pbits=(1<<len(P))-1
assert all(not (x&y==x) for x,y in itertools.permutations(rows,2))
raw=[sum((x>>i&1)<<j for j,x in enumerate(rows)) for i in range(8)]
cost=(d/'mono.bin').read_bytes()
def index(s):return ((~s&pbits)<<len(N)) | (s>>len(P))
def price(s):return cost[index(s)]-1
levels=[set(raw)|{0,allbits}];used=levels[0].copy()
def hist(xs):
 xs=list(xs);return {v:sum(price(x)==v for x in xs) for v in sorted(set(map(price,xs)))}
for k in range(1,9):
 fresh=set()
 for i in range((k-1)//2+1):
  for a in levels[i]:
   for b in levels[k-1-i]:fresh.update((a&b,a|b))
 levels.append(fresh-used);used.update(fresh)
print('raw',list(map(price,raw)))
out={'positive':P,'negative':N,'raw_repair_cost':list(map(price,raw)),'prefix_formula_hist':[]}
for k,L in enumerate(levels):
 h=hist(L);print(k,len(L),h,flush=True);out['prefix_formula_hist'].append(h)
out['worst_traces']=[s for s in range(1<<20) if price(s)==14]
(d/'census.json').write_text(json.dumps(out,indent=2))
