"""Replay the 64 small inverter cases with only exact integer operations."""
from pathlib import Path
import itertools,json
p=Path(__file__).resolve().parent
data=json.loads((p/'small-certs.json').read_text())
C=(p/'mono.bin').read_bytes()
edges=[17,33,34,36,65,66,72,80,129,132,144,160]
def f(x):return any(x&e==e for e in edges)
N=[x for x in range(256) if not f(x) and all(f(x|1<<i) for i in range(8) if not x>>i&1)]
assert len(N)==7
from functools import lru_cache
@lru_cache(None)
def cap(index,signal):
    d=data['matrices'][index]
    P,N,W=d['P'],d['N'],d['weights']
    assert all(f(x) for x in P) and all(not f(x) for x in N)
    assert len(set(P))==len(P) and len(set(N))==len(N) and len(W)==len(P)
    assert all(len(row)==len(N) and all(type(v)==int for v in row) for row in W)
    mat=[[W[i][j] for j,y in enumerate(N) if not (signal>>y)&1] for i,x in enumerate(P) if (signal>>x)&1]
    if not mat or not mat[0]:return 0
    if len(mat)>len(mat[0]):mat=list(zip(*mat))
    best=0
    for mask in range(1<<len(mat)):
        cols=map(sum,zip(*(row for r,row in enumerate(mat) if mask>>r&1)))
        best=max(best,sum(max(t,0) for t in cols))
    return best
raw=[sum(((x>>j)&1)<<x for x in range(256)) for j in range(8)]
cases=[(1,a) for a in raw]+[(2,v) for a,b in itertools.combinations(raw,2) for v in (a&b,a|b)]
seen=set()
for k,h in cases:
    assert h not in seen
    seen.add(h)
    a=sum(((h>>x)&1)<<j for j,x in enumerate(edges));b=sum((1-((h>>x)&1))<<j for j,x in enumerate(N))
    if 1+max(C[128*a+127],C[128*4095+b])>=15-k:continue
    idx=data['assignment'][hex(h)]
    total=sum(map(sum,data['matrices'][idx]['weights']))
    top=max(cap(idx,s) for s in raw+[~h])
    assert total>(14-k)*top
assert len(seen)==64
print('verified all 8 raw and 56 two-leaf inverter inputs')
