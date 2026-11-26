"""Independently verify the integer rectangle dual and its matching monotone formula."""
from pathlib import Path
import itertools,json
d=Path(__file__).parent
mask=386990
pos=[k for k in range(24) if mask>>k&1]
neg=[k for k in range(24) if not mask>>k&1]
weights=json.loads((d/'weights.json').read_text())['weights']
assert len(weights)==len(pos) and all(len(row)==len(neg) and all(type(v) is int for v in row) for row in weights)
def on(k):return {k//6,4+k%6}
largest=0;count=0
for v in range(10):
 rows=[r for r,k in enumerate(pos) if v in on(k)]
 cols=[c for c,k in enumerate(neg) if v not in on(k)]
 for subset in range(1,1<<len(rows)):
  sums=[sum(weights[r][c] for j,r in enumerate(rows) if subset>>j&1) for c in cols]
  largest=max(largest,sum(max(0,x) for x in sums))
  count+=(1<<len(cols))-1
assert sum(map(sum,weights))==13 and largest==1
# A syntax tree duplicates its shared three-column disjunction.
form=('or',('and',('or',1,2),('or',('or',5,6),('or',7,8))),
           ('and',('or',0,4),('or',('or',5,6),('or',7,('or',9,3)))))
def check(t,k):
 if isinstance(t,int):return (t in on(k)),1
 a,n=check(t[1],k);b,m=check(t[2],k)
 return (a and b if t[0]=='and' else a or b),n+m
for k in range(24):
 value,leaves=check(form,k)
 assert leaves==13 and value==bool(mask>>k&1)
print('signed weight 13, maximum 1 over',count,'nonempty labeled rectangles; 13-leaf formula on 24 inputs')
