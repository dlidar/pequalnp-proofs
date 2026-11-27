"""Independent integer replay of all boundary and leaf-rectangle inequalities."""
import json,itertools
from pathlib import Path
p=Path(__file__).resolve().parent
D=json.loads((p/'bounds.json').read_text()); E=D['edges']
def target(x):return any(x&(1<<i) and x&(1<<j) for i,j in E)
raw=[sum(((x>>i)&1)<<x for x in range(256)) for i in range(8)]
signals=raw+[v for a,b in itertools.combinations(raw,2) for v in (a&b,a|b)]
def rectangle_cap(d,h):
    W,N=d['weights'],d['N'];mat=[[w for j,w in enumerate(row) if not (h>>N[j])&1] for x,row in zip(d['P'],W) if (h>>x)&1]
    if not mat or not mat[0]:return 0
    if len(mat)>len(mat[0]):mat=list(zip(*mat))
    sums=[tuple(0 for _ in mat[0])]
    for row in mat:sums += [tuple(a+b for a,b in zip(row,s)) for s in sums]
    return max(sum(max(0,v) for v in s) for s in sums)
def check():
    cert=json.loads((p/'weights-32249.json').read_text());assert set(cert)=={hex(h) for h in signals}
    for h in signals:
        d=cert[hex(h)];rs,cs,W=d['P'],d['N'],d['weights']
        assert len(rs)==len(W)==len(set(rs)) and len(cs)==len(set(cs))
        assert all(len(r)==len(cs) and all(type(v)==int for v in r) for r in W)
        assert all(target(x) for x in rs) and all(not target(y) for y in cs)
        it=sum(map(sum,W));cap=max(rectangle_cap(d,g) for g in raw+[~h])
        assert cap==d['cap'] and it==d['total'] and it>(14 if h in raw else 13)*cap
    print('64 signed integer certificates give 15 leaves with an inverted raw bit and at least 14 with a complemented pair even with reusable complemented signal')
if __name__=='__main__':check()
