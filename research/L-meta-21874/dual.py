from fractions import Fraction
from math import lcm
from pathlib import Path
import json,itertools,numpy as np
from scipy.optimize import linprog
m=386990;P=[i for i in range(24) if m>>i&1];N=[i for i in range(24) if not(m>>i&1)]
A=len(P);B=len(N)
def on(i,r):return i in (r//6,4+r%6)
def cuts(x):
    for i in range(10):
        I=[a for a,p in enumerate(P) if on(i,p)]
        J=[b for b,n in enumerate(N) if not on(i,n)]
        for k in range(1,len(I)+1):
            for T in itertools.combinations(I,k):
                col=x[list(T),:].sum(axis=0)
                U=tuple(j for j in J if col[j]>0)
                yield T,U,sum(col[j] for j in U)
rows=[];seen=set()
for iteration in range(180):
    res=linprog(-np.ones(A*B),A_ub=np.array(rows) if rows else None,b_ub=np.ones(len(rows)) if rows else None,bounds=(-5,1),method='highs')
    assert res.success
    x=res.x.reshape(A,B)
    for T,U,total in cuts(x):
        if total<=1.000001 or (T,U) in seen:continue
        row=np.zeros((A,B));row[np.ix_(T,U)]=1;rows.append(row.ravel());seen.add((T,U))
    gaps=max(s for _,_,s in cuts(x))
    if gaps<=1.000001 or x.sum()>11*gaps+1e-6:
        f=[Fraction(float(v)).limit_denominator(100) for v in x.ravel()]
        D=lcm(*(v.denominator for v in f));z=np.array([int(v*D) for v in f],dtype=object).reshape(A,B)
        mx=max(v for _,_,v in cuts(z));total=sum(z.ravel())
        print('total',total,'largest rectangle',mx,'ratio',str(Fraction(total,mx)),flush=True)
        Path(__file__).with_name('weights.json').write_text(json.dumps(dict(weights=z.tolist(),total=int(total),maximum=int(mx)))+'\n')
        break
