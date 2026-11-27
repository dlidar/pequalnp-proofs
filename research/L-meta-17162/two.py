"""Find signed rectangle certificates for every two-gate monotone preprocessor."""
from itertools import combinations
from pathlib import Path
from functools import lru_cache
import json, numpy as np
import weights
p=Path(__file__).resolve().parent

def solve_core(cols):
    weights.set_core(cols)
    n=weights.n; P=weights.P; N=weights.N
    tag='-'.join(map(str,cols))
    raw=lambda inputs:[sum((x>>i&1)<<j for j,x in enumerate(inputs)) for i in range(n)]
    pr,nr=raw(P),raw(N)
    def signals(pair):
        a,b=list(pr),list(nr); ss=[]
        for op,i,j in pair:
            for vals in (a,b):vals.append((vals[i]&vals[j]) if op=='and' else (vals[i]|vals[j]))
            ss.append((a[-1],b[-1]))
        return tuple(ss)
    def gates(k):
        return [(op,i,j) for i,j in combinations(range(k),2) for op in ('and','or')]
    def trans(gate,g):
        o,i,j=gate
        return (o,*sorted((g[i],g[j] if j<n else n)))
    pairs=[]
    for c in sorted({min(trans(k,g) for g in weights.G) for k in gates(n)}):
        stab=[g for g in weights.G if trans(c,g)==c]
        pairs.extend((c,d) for d in sorted({min(trans(k,g) for g in stab) for k in gates(n+1)}))
    traces=[signals(pair) for pair in pairs]; goal=len(P)+2
    sources=json.loads((p/('duals-'+tag+'.json')).read_text());left=set(range(len(pairs)))
    @lru_cache(None)
    def rectangles(signal):
        a,b=signal;rs=[i for i in range(len(P)) if a>>i&1];cs=[j for j in range(len(N)) if not b>>j&1]
        return rs,cs,np.array([[(k>>i)&1 for i in range(len(rs))] for k in range(1<<len(rs))],dtype=np.int64)
    def score(w,s):
        r,c,sub=rectangles(s)
        if not r or not c:return 0
        return np.maximum(sub@w[np.ix_(r,c)],0).sum(axis=1).max()
    seen=set(); extra=[]
    def use(record):
        total=record['total']; rawcap=record['scale']; W=np.array(record['weights'],dtype=np.int64)
        if total <= (goal-1)*rawcap:return
        for g in weights.G:
            if not left:return
            rows=[P.index(weights.maskmap(x,g)) for x in P]
            cols=[N.index(weights.maskmap(x,g)) for x in N]
            w=W[np.ix_(rows,cols)];buf=w.tobytes()
            if buf in seen:continue
            seen.add(buf)
            @lru_cache(None)
            def ok(s):return total>(goal-1)*score(w,s)
            left.difference_update([i for i in left if all(ok(s) for s in traces[i])])
    for rec in sources:use(rec)
    print(tag,'orbits',len(pairs),'remaining',len(left),flush=True)
    for i in sorted(left):
        if i not in left:continue
        record=weights.solve_program(pairs[i]);extra.append(record)
        use(record)
    (p/('extra-'+tag+'.json')).write_text(json.dumps(extra,separators=(',',':')))
    print(tag,'remaining after refinement',len(left),'extra',len(extra),flush=True)
if __name__=='__main__':
    for c in weights.graphs():solve_core(c)
