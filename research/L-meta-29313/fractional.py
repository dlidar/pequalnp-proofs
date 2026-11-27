from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix
import json
p=Path(__file__).resolve().parent
data=json.loads((p/'mono-weights.json').read_text());P,N,w=[data[k] for k in ['P','N','weights']]
C=len(N);R=len(P)
def submasks(mask):
    a=mask
    while a:yield a;a=(a-1)&mask
boxes=set()
for i in range(8):
    rows=sum(1<<j for j,x in enumerate(P) if x>>i&1)
    cols=sum(1<<j for j,x in enumerate(N) if not (x>>i&1))
    for a in submasks(rows):
        for b in submasks(cols):
            box=sum(b<<(j*C) for j in range(R) if a>>j&1)
            boxes.add(box)
boxes=sorted(boxes)
A=csc_matrix(np.array([[(box>>j)&1 for j in range(R*C)] for box in boxes],dtype=np.float64).T)
res=linprog(np.ones(len(boxes)),A_eq=A,b_eq=np.ones(R*C),bounds=(0,None),method='highs')
assert res.success
x={hex(box):str(Fraction(float(v)).limit_denominator(100000)) for box,v in zip(boxes,res.x) if v>1e-9}
for j in range(R*C):assert sum(Fraction(q) for b,q in x.items() if int(b,16)>>j&1)==1
result=sum(map(Fraction,x.values()));print(result,len(x))
assert result==Fraction(data['total'],data['cap'])
(p/'fractional-partition.json').write_text(json.dumps(x))
