"""List all minimum-width monotone encoders for the two five-signal balanced cuts."""
from cutwidth import *
from itertools import combinations
def encoders(t):
 vertices=[i for i in range(8) if t>>i&1]
 xs=masks(t)
 def index(x):return sum(((x>>v)&1)<<j for j,v in enumerate(vertices))
 assert [index(x) for x in xs]==list(range(16))
 pts,_=problem(t);pairs=[(index(x),index(y)) for x,y in pts];full=(1<<len(pts))-1
 inputs=[sum(((x>>i)&1)<<x for x in range(16)) for i in range(4)]
 seen=set(inputs);layer=set(inputs)
 while layer:
  new={op for a in layer for b in seen for op in (a&b,a|b)}-seen;seen|=new;layer=new
 assert len(seen)==166
 hits={f:sum(1<<j for j,(a,b) in enumerate(pairs) if f>>a&1 and not f>>b&1) for f in seen}
 w=json.loads((p/'cutwidth.json').read_text())[str(t)]['width']
 options=[]
 for fs in combinations(sorted(seen),w):
  v=0
  for f in fs:v|=hits[f]
  if v==full:options.append(fs)
 return options
if __name__=='__main__':
 ds={t:encoders(t) for t in (83,172,86,169)}
 for t,v in ds.items():print(t,len(v))
 (p/'balanced-encoders.json').write_text(json.dumps(ds))
