"""Independent integer check of the gate potential and all selected restrictions."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
p=Path(__file__).resolve().parent
rows,c,raw,target=json.loads((p/'cost.json').read_text())
assert c[0]==c[255]==0 and all(c[v]==1 for v in raw) and c[target]==5
assert all(c[a]==c[255-a] for a in range(256))
assert all(max(c[a&b],c[a|b])<=c[a]+c[b] for a in range(256) for b in range(256))
terms=[(0,4,8),(0,5,7),(1,3,8),(1,5,6),(2,3,7),(2,4,6)]
def perm(x):return any(all(x>>j&1 for j in t) for t in terms)
cuts=json.loads((p/'restrictions.json').read_text())
free=[]
for pre,order in cuts:
    assert len(set(order))==4 and all(not pre>>j&1 for j in order)
    full=[pre|sum(1<<j for k,j in enumerate(order) if x>>k&1) for x in range(16)]
    assert all(perm(u)==any((x&m)==m for m in (5,10,6)) for x,u in enumerate(full))
    assert all(len({(u&pair)==pair for u in full})==1 for pair in (3,288))
    xs=[full[x] for x in rows];sigs=[sum(1<<t for t,u in enumerate(xs) if u>>j&1) for j in range(9)]
    sigs += [sigs[0]&sigs[1],sigs[5]&sigs[8]]
    assert sum(c[v] for v in sigs)==4
    assert sum(1<<t for t,u in enumerate(xs) if perm(u))==target
    free.append(set(order))
assert len(cuts)==32
assert all(any(j not in f for f in free) for j in range(9))
hits=[pair for pair in combinations(range(9),2) if all(set(pair)&f for f in free)]
assert hits==[(3,7),(4,6)]
print('65536 binary pairs, 256 complements, 32 restrictions, two minimum hitting pairs verified.')
