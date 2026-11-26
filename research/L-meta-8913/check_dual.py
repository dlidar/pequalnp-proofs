"""Check the integral cover certificate independently of the optimizer."""
from pathlib import Path
import json
from merged_stars import edges
W = Path(__file__).resolve().parent
tests = json.loads((W/'design.json').read_text())
weights = [int(x) for x in json.loads((W/'cover-dual.json').read_text())]
blocks = json.loads((W/'optimal-blocks.json').read_text())
assert len(weights) == len(edges) == 52 and min(weights) >= 0 and sum(weights) == 49
# For fixed point subset P, a safe rectangle may use precisely the lines allowed
# below. Include each allowed line of positive excess to maximize weight minus cost.
for pset in range(1,1<<13):
    allowed = (1<<13)-1
    for p,l in tests:
        if p & pset:
            allowed &= ~l
    by_line=[0]*13
    for (i,j),v in zip(edges,weights):
        if pset>>i&1:
            by_line[j]+=v
    assert sum(max(0,v-1) for j,v in enumerate(by_line) if allowed>>j&1)<=pset.bit_count()
for side in (0,1):
    for i in range(13):
        if all(not t[side]>>i&1 for t in tests):
            assert sum(v for e,v in zip(edges,weights) if e[side]==i)<=1
def accepts(p,l):
    return any((not P or any(p>>i&1 for i in P)) and (not L or any(l>>j&1 for j in L))
               for P,L in blocks)
assert all(P or L for P,L in blocks)
assert all((P and L) or len(P)+len(L)==1 for P,L in blocks)
assert all(accepts(1<<p,1<<l) for p,l in edges) and all(not accepts(p,l) for p,l in tests)
assert sum(len(P)+len(L) for P,L in blocks)==49
print('Exact optimum: 49 leaves, 48 gates for an unshared OR of rectangles and raw singletons.')
