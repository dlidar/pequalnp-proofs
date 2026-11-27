"""Independent checker for a lower certificate and a 15-piece partition."""
from pathlib import Path
import json,itertools
p=Path(__file__).resolve().parent
D=json.loads((p/'mono-weights.json').read_text());P,N,W=D['P'],D['N'],D['weights']
edges=json.loads((p/'bounds.json').read_text())['edges']
def target(x):
    return any((x>>i)&(x>>j)&1 for i,j in edges)
assert all(target(x) for x in P) and all(not target(x) for x in N)
R,C=len(P),len(N); cap=D['cap']; weights=sum(W,[])
def subsets(xs):
    return itertools.chain.from_iterable(itertools.combinations(xs,k) for k in range(1,len(xs)+1))
def rectangle(rows,cols):return sum(1<<(i*C+j) for i in rows for j in cols)
allowed={}
for bit in range(8):
    rows=[i for i,x in enumerate(P) if x&(1<<bit)]
    cols=[j for j,x in enumerate(N) if not x&(1<<bit)]
    for rs in subsets(rows):
        for cs in subsets(cols):
            cost=cap-sum(W[i][j] for i in rs for j in cs)
            assert cost>=0
            allowed[rectangle(rs,cs)]=cost
full=(1<<(R*C))-1
score=sum(weights);initial=14*cap-score
assert 0<=initial<cap
by_cell=[[entry for entry in allowed.items() if entry[1]<=initial and entry[0]&(1<<i)] for i in range(R*C)]
proved=set()
for mask,k,slack,pivot in json.loads((p/'partition-trace.json').read_text()):
    s=int(mask,16)
    assert s&full==s and 0<=slack<=initial and 0<=k<=14
    if pivot==-1:assert (not k) != (not s)
    else:
        assert k and 0<=pivot<R*C and s>>pivot&1
        for box,d in by_cell[pivot]:
            if s&box==box and d<=slack:
                assert (s^box,k-1,slack-d) in proved
    proved.add((s,k,slack))
assert (full,14,initial) in proved
gates=json.loads((p/'upper.json').read_text())['gates']
def evaluate(x):
    vals=[(x>>i)&1 for i in range(8)]
    for op,i,j in gates:vals.append((vals[i]&vals[j]) if op=='and' else (vals[i]|vals[j]))
    return vals
vals={x:evaluate(x) for x in P+N}
def partition(g,rows,cols):
    if not rows or not cols:return []
    assert all(vals[P[i]][g] for i in rows) and all(not vals[N[j]][g] for j in cols)
    if g<8:return [rectangle(rows,cols)]
    op,a,b=gates[g-8]
    if op=='or':
        left=[i for i in rows if vals[P[i]][a]]
        return partition(a,left,cols)+partition(b,[i for i in rows if i not in left],cols)
    left=[j for j in cols if not vals[N[j]][a]]
    return partition(a,rows,left)+partition(b,rows,[j for j in cols if j not in left])
upper=partition(8+len(gates)-1,list(range(R)),list(range(C)))
assert len(upper)==15
covered=0
for box in upper:
    assert box in allowed and not box&covered
    covered|=box
assert covered==full
print('exactly 15 monochromatic rectangles;',len(proved),'verified trace nodes;',len(allowed),'eligible rectangles before weight pruning')
from fractions import Fraction
fractional={int(k,16):Fraction(v) for k,v in json.loads((p/'fractional-partition.json').read_text()).items()}
assert all(b in allowed and z>0 for b,z in fractional.items())
for cell in range(R*C):
    assert sum(v for b,v in fractional.items() if b>>cell&1)==1
assert sum(fractional.values())==Fraction(score,cap)==Fraction(105,8)
# If the set of admissible input labels for a cell is a singleton, every
# cover needs a rectangle of that label. All eight labels occur this way.
diff={x & (255 ^ y) for x in P for y in N}
assert 0 not in diff and all(1<<i in diff for i in range(8))
print('overlapping cover 8; fractional partition 105/8 from',len(fractional),'weighted rectangles')
