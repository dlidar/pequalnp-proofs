"""Signed Karchmer-Wigderson rectangle lower bounds for four-row incidence cores."""
from fractions import Fraction
from math import lcm
from itertools import permutations,combinations
from functools import reduce
from pathlib import Path
import json
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
p=Path(__file__).resolve().parent
from core import graphs
def set_core(cols):
    global E,P,N,G,n
    n=4+len(cols)
    E=[(i,4+j) for j,v in enumerate(cols) for i in range(4) if v>>i&1]
    P=[(1<<a)|(1<<b) for a,b in E]
    def fun(x):return any(x&m==m for m in P)
    N=[x for x in range(1<<n) if not fun(x) and all(fun(x|1<<i) for i in range(n) if not x>>i&1)]
    G=[]
    for f in permutations(range(4)):
        im=[sum(1<<f[i] for i in range(4) if v>>i&1) for v in cols]
        if all(v in cols for v in im):G.append((*f,*(4+cols.index(v) for v in im)))
def maskmap(mask,g):return sum(1<<g[i] for i in range(n) if mask>>i&1)
def key(c):return (c[0],*sorted(c[1:]))
def movecache(cs,g):return tuple(sorted(key((op,g[i],g[j])) for op,i,j in cs))
def opval(c,x):
    op,i,j=c
    a,b=(x>>i)&1,(x>>j)&1
    return a&b if op=='and' else a|b
def solve_program(cs):
    def move(c,g):
        op,a,b=c
        return (op,*sorted((g[a],g[b] if b<n else b)))
    def trace(x):
        w=[(x>>i)&1 for i in range(n)]
        for op,a,b in cs:w.append((w[a]&w[b]) if op=='and' else (w[a]|w[b]))
        return w[n:]

    stabilizer=[g for g in G if tuple(move(c,g) for c in cs)==cs]
    index={};mult=[]
    for a in P:
        for b in N:
            if (a,b) in index:continue
            o={(maskmap(a,g),maskmap(b,g)) for g in stabilizer}
            for xy in o:index[xy]=len(mult)
            mult.append(len(o))
    lab=np.array([[index[a,b] for b in N] for a in P],dtype=int);nr=len(mult)
    sigs=[([a>>i&1 for a in P],[b>>i&1 for b in N]) for i in range(n)]
    sigs += [([trace(a)[j] for a in P],[trace(b)[j] for b in N]) for j in range(len(cs))]
    subsets=[]
    for pos,neg in sigs:
        rows=[i for i,b in enumerate(pos) if b];cols=[i for i,b in enumerate(neg) if not b]
        for k in range(1,len(rows)+1):
            for A in combinations(rows,k):
                subsets.append(lab[np.ix_(A,cols)])
    planes=[];seen=set()
    def vec(ids):return np.bincount(ids.ravel(),minlength=nr)
    def add(h):
        t=tuple(map(int,h))
        if t not in seen:planes.append(h);seen.add(t);return True
        return False
    for a in subsets:add(vec(a))
    while True:
        lp=linprog([-x for x in mult],A_ub=np.asarray(planes),b_ub=np.ones(len(planes)),bounds=(-20,20),method='highs')
        assert lp.success
        altered=False
        for tbl in subsets:
            vals=lp.x[tbl].sum(axis=0);mask=vals>0
            if vals[mask].sum()>1.0000001:altered|=add(vec(tbl[:,mask]))
        if not altered:break
    weights=[Fraction(float(x)).limit_denominator(10000) for x in lp.x];scale=reduce(lcm,(x.denominator for x in weights),1)
    iv=[int(w*scale) for w in weights]
    assert all(sum(max(0,sum(iv[j] for j in col)) for col in tbl.T)<=scale for tbl in subsets)
    total=sum(a*b for a,b in zip(iv,mult)); flat=[[iv[i] for i in row] for row in lab]
    return dict(caches=cs,scale=scale,total=total,lower=(total+scale-1)//scale,weights=flat)
if __name__=='__main__':
    for cols in graphs():
        set_core(cols)
        caches=[(op,a,b) for a,b in combinations(range(n),2) for op in ['and','or']]
        reps=sorted({min(movecache((c,),g) for g in G) for c in caches})
        results=[]
        for rep in [(),*reps]:
            r=solve_program(rep)
            results.append(r)
        target=len(E)+4
        print(cols, 'raw',results[0]['lower'],'min with one cached',min(r['lower'] for r in results[1:]),'reference leaves',target,flush=True)
        (p/('duals-'+'-'.join(map(str,cols))+'.json')).write_text(json.dumps(results,separators=(',',':')))
