import itertools,json
from pathlib import Path
p=Path(__file__).resolve().parent
D=json.loads((p/'bounds.json').read_text());E=D['positive'];N=D['negative']
C=(p/'mono.bin').read_bytes()
raw=[sum(((x>>i)&1)<<x for x in range(256)) for i in range(8)]
cases=[(1,'raw',i,i,a) for i,a in enumerate(raw)]+[(2,k,i,j,h) for i,j in itertools.combinations(range(8),2) for k,h in [('and',raw[i]&raw[j]),('or',raw[i]|raw[j])]]
def graph(x):return any(x&e==e for e in E)
def pin(h):
 a=sum(((h>>x)&1)<<j for j,x in enumerate(E));b=sum((1-((h>>x)&1))<<j for j,x in enumerate(N))
 return 1+max(C[64*a+63],C[64*8191+b])
def lift(h):
 enc=[x+256*(1-((h>>x)&1)) for x in range(256)]
 pos=[x for x in range(256) if graph(x)]
 neg=[x for x in range(256) if not graph(x)]
 return [x for x in pos if not any(x!=y and enc[x]&enc[y]==enc[y] for y in pos)], [x for x in neg if not any(x!=y and enc[x]&enc[y]==enc[x] for y in neg)]
if __name__=='__main__':
 for k,op,i,j,h in cases:
  if pin(h)>=15-k:continue
  P,B=lift(h)
  print(op,i,j,pin(h),len(P),len(B))
