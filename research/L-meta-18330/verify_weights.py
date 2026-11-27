"""Replay all signed rectangle certificates with Python integers, without an optimizer."""
from collections import Counter
from functools import lru_cache
from itertools import permutations,combinations
from pathlib import Path
import gzip,json
p=Path(__file__).resolve().parent
edges=[(i,7+j) for i in range(7) for j in range(7) if (i-j)%7 in (0,1,3)]
P=[1<<i|1<<j for i,j in edges]
def target(x):return any((x&a)==a for a in P)
N=[x for x in range(16384) if not target(x) and all(target(x|1<<i) for i in range(14) if not (x>>i)&1)]
assert len(N)==37
lines=[{i for i,j in edges if j==7+k} for k in range(7)]
G=[]
for f in permutations(range(7)):
    mapped=[{f[i] for i in L} for L in lines]
    if all(m in lines for m in mapped):
        g=f+tuple(7+lines.index(m) for m in mapped);G.extend([g,tuple(7+(-i)%7 if i<7 else (-i)%7 for i in g)])
assert len(G)==len(set(G))==336
def move(c,g):
    op,i,j=c;return (op,*sorted((g[i],g[j] if j!=14 else 14)))
def perm(x,g):return sum(1<<g[i] for i in range(14) if x>>i&1)
def atom(rows,i):return tuple((r>>i)&1 for r in rows)
def gate(op,x,y):return tuple((u&v) if op=='and' else (u|v) for u,v in zip(x,y))
raw=[(atom(P,i),atom(N,i)) for i in range(14)]
def trace(c,w):
    op,i,j=c;return tuple(gate(op,a,b) for a,b in zip(w[i],w[j]))
def maximum(w,s):
    """Max over every subset of eligible rows and every subset of eligible columns."""
    pos,neg=s;rs=[i for i,v in enumerate(pos) if v];cs=[i for i,v in enumerate(neg) if not v]
    v=[0]*len(cs);best=0
    def visit(t):
        nonlocal best
        if t==len(rs):best=max(best,sum(max(z,0) for z in v));return
        visit(t+1)
        row=w[rs[t]]
        for j,c in enumerate(cs):v[j]+=row[c]
        visit(t+1)
        for j,c in enumerate(cs):v[j]-=row[c]
    visit(0);return best
def check(w,cap,sigs):
    assert len(w)==21 and all(len(row)==37 and all(type(v)==int for v in row) for row in w)
    assert cap>0 and max(maximum(w,s) for s in set(sigs))<=cap
    return (sum(map(sum,w))+cap-1)//cap

orig=json.loads((p/'kw.json').read_text())
for r in orig:
    signals=raw+[trace(c,raw) for c in r['caches']]
    assert sum(map(sum,r['weights']))==r['total'] and check(r['weights'],r['scale'],signals)==r['lower']
certs=json.loads(gzip.decompress((p/'two-certificates.json.gz').read_bytes()))
assert len(certs)==260
cover=set()
for r in certs:
    pair=tuple(tuple(c) for c in r['pair'])
    orbit={tuple(move(c,g) for c in pair) for g in G}
    assert not cover.intersection(orbit);cover.update(orbit)
    w=r.get('weights')
    if w is None:
        ix,gi=r['source'];base=orig[ix]['weights'];g=G[gi]
        rp=[P.index(perm(x,g)) for x in P];cp=[N.index(perm(x,g)) for x in N]
        w=[[base[i][j] for j in cp] for i in rp]
    signals=raw[:]
    for c in pair:signals.append(trace(c,signals))
    assert check(w,r['cap'],signals)>=26
choices=lambda n:[(op,i,j) for op in ('and','or') for i,j in combinations(range(n),2)]
assert cover=={(a,b) for a in choices(14) for b in choices(15)}
print(len(cover),'two-gate programs verified from',len(certs),'orbit representatives',flush=True)

# Replay the triple certificates. Enumerate monotone truth tables directly.
values=[t for t in range(256) if all(not(t>>i&1) or (t>>j&1) for i in range(8) for j in range(8) if i&j==i)]
assert len(values)==20
triples=set();hist=Counter()
for line in (p/'scope.jsonl').read_text().splitlines():
    r=json.loads(line);tri=tuple(r['inputs']);orbit={tuple(sorted(g[i] for i in tri)) for g in G}
    assert not triples.intersection(orbit);triples.update(orbit)
    def proj(x):return sum(((x>>i)&1)<<k for k,i in enumerate(tri))
    sigs=raw+[(tuple((f>>proj(x))&1 for x in P),tuple((f>>proj(x))&1 for x in N)) for f in values if f not in (0,255)]
    lb=check(r['weights'],r['cap'],sigs);assert lb==r['lower']
    # Factor the seven stars by each of the two orientations. When a star has
    # multiple leaves on the triple, their OR costs one free decoder leaf.
    ub=28
    for side in (range(7),range(7,14)):
        cost=0
        for i in side:
            neighbors=[b if i==a else a for a,b in edges if i==a or i==b]
            internal=set(neighbors).intersection(tri)
            cost+=1+len(set(neighbors)-internal)+int(bool(internal))
        ub=min(ub,cost)
    assert ub==lb
    hist[lb]+=len(orbit)
assert triples==set(combinations(range(14),3))
print('all',len(triples),'triples; exact decoder leaves and frequencies',sorted(hist.items()),flush=True)
approx=json.loads((p/'nearest.json').read_text())
gates=approx['gates']
assert len(gates)==25
for j,(op,a,b) in enumerate(gates): assert op in ('and','or') and 0<=a<b<14+j
fn=fp=0
for x in range(16384):
    w=[bool(x>>i&1) for i in range(14)]
    for op,a,b in gates: w.append(w[a] and w[b] if op=='and' else w[a] or w[b])
    fn+=int(target(x) and not w[-1]);fp+=int(not target(x) and w[-1])
assert (fn,fp)==(68,18)==(approx['fn'],approx['fp'])
print('25-gate approximation checked on 16384 inputs:',fn,'false negatives and',fp,'false positives')
