"""A changed edge is independently visible on its own two-vertex input."""
from itertools import combinations
from pathlib import Path
import json
p=Path(__file__).resolve().parent
E={tuple(e) for e in json.loads((p/'bounds.json').read_text())['edges']}
pairs=list(combinations(range(8),2))
def f(edges):
 return sum(1<<x for x in range(256) if any(x>>i&x>>j&1 for i,j in edges))
true=f(E);out=[]
for k in (1,2):
 for delta in combinations(pairs,k):
  mask=true^f(E^set(delta))
  if mask.bit_count()<=2:out.append((delta,[i for i in range(256) if mask>>i&1]))
(p/'nearest.json').write_text(json.dumps(out))
print('distance <=2:',out)
