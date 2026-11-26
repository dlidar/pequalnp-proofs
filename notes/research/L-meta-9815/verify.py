"""Check each published integer certificate and every constructive cache witness."""
from itertools import combinations
from pathlib import Path
from fractions import Fraction
import gzip,json
here=Path(__file__).resolve().parent
data=json.loads(gzip.decompress((here/'weights.json.gz').read_bytes()))
rows=data['rows'];cols=data['cols']
edges=[(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
masks=[(1<<a)|(1<<b) for a,b in edges]
truth=[any(x&m==m for m in masks) for x in range(1<<14)]
assert set(masks)==set(rows) and len(rows)==19
assert [x for x,v in enumerate(truth) if not v and all(truth[x|(1<<i)] for i in range(14) if not x>>i&1)]==cols
def profile(fn):
    return ([j for j,y in enumerate(rows) if fn(y)],[j for j,z in enumerate(cols) if not fn(z)])
raw=[profile(lambda x: x>>i&1) for i in range(14)]
def check(d,label=None,inverted=False):
    wt=d['weights'];cap=d['cap'];total=d['total']
    assert all(len(r)==36 for r in wt) and len(wt)==19 and sum(map(sum,wt))==total
    for rs,cs in raw+([profile(label)] if label and not inverted else []):
        for k in range(1,len(rs)+1):
            for subset in combinations(rs,k):
                assert sum(max(0,sum(wt[i][j] for i in subset)) for j in cs)<=cap
    if inverted:
        rs,cs=profile(label)
        assert sum(max(0,wt[i][j]) for i in rs for j in cs)<=cap
    return -(-total//cap)
def star_for_pair(a,b):
    centers=list(range(7,14)) if b<7 else list(range(7))
    term=[];rawleaves=0;cachecount=0
    for c in centers:
        neighbors=[j if i==c else i for i,j in edges if c in (i,j)]
        if a in neighbors and b in neighbors:
            term.append((c,[i for i in neighbors if i not in (a,b)],True))
            rawleaves+=1+len(neighbors)-2;cachecount+=1
        else:
            term.append((c,neighbors,False));rawleaves+=1+len(neighbors)
    assert rawleaves+cachecount==25 and cachecount==1
    for x in range(16384):
        signal=bool(x&(1<<a) or x&(1<<b))
        assert truth[x]==any((x>>c&1) and ((use and signal) or any(x>>i&1 for i in ids)) for c,ids,use in term)
assert check(data['baseline'])==26
expected={(op,a,b) for op in ('and','or') for a,b in combinations(range(14),2)}
neigh=[{b if a==i else a for a,b in edges if i in (a,b)} for i in range(14)]
useful=0
for d in data['binary']:
    op,a,b=d['op'],d['a'],d['b'];expected.remove((op,a,b))
    fn=lambda x: ((x>>a&1) | (x>>b&1)) if op=='or' else ((x>>a&1) & (x>>b&1))
    lower=check(d,fn)
    saving=op=='or' and any({a,b}<=ls for ls in neigh)
    assert lower==26-int(saving)
    if saving:star_for_pair(a,b);useful+=1
assert not expected and useful==34
assert sorted(d['i'] for d in data['inverters'])==list(range(14))
for d in data['inverters']:
    assert check(d,lambda x: not(x>>d['i']&1),True)==26
print('Verified ordinary 26 leaves, 34 useful binary caches at 25 leaves, 148 other binary caches and 14 inverted inputs at 26. All 34 witnesses passed on every input.')
