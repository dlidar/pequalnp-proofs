import itertools,json,math
from pathlib import Path
w=Path(__file__).resolve().parent
E=list(itertools.combinations(range(6),2))
T=[tuple(E.index(e) for e in itertools.combinations(v,2)) for v in itertools.combinations(range(6),3)]
M=[sum(1<<j for j in t) for t in T]
def hit(covered):
 for size in range(7):
  for edges in itertools.combinations(range(15),size):
   if all(any(i in T[j] for i in edges) for j in covered):return edges
def build(covered,H):
 groups={e:[] for e in H};g=[]
 def gate(op,a,b=None):
  g.append((op,a,b));return 14+len(g)
 def fold(op,ws):
  a=ws[0]
  for b in ws[1:]:a=gate(op,a,b)
  return a
 # Complement of the triangle formula on missing edges, with one final NOT.
 for j in covered:
  e=next(e for e in H if e in T[j]); a,b=sorted(set(T[j])-{e})
  groups[e].append(gate('or',a,b))
 out=fold('and',[gate('or',e,fold('and',ls)) for e,ls in groups.items() if ls])
 return g,gate('not',out)
def ev(g,o,x):
 a=[(x>>i)&1 for i in range(15)]
 for op,i,j in g:
  a.append((1-a[i]) if op=='not' else (a[i]|a[j] if op=='or' else a[i]&a[j]))
 return a[o]
if __name__=='__main__':
 import collections
 rows=[sum(1<<i for i,m in enumerate(M) if not x&m) for x in range(1<<15)]
 H=hit(range(20));g,out=build(list(range(20)),H)
 assert len(g)==46 and all(ev(g,out,x)==bool(r) for x,r in enumerate(rows))
 (w/'reference.json').write_text(json.dumps(dict(gates=g,out=out,cover=H)))
 print('exact',len(g),'all',len(rows),'cover',H,flush=True)
 counts=collections.Counter(rows)
 # For 42 total gates, an omission design with 18 triangles permits six owners.
 best=None;hist=collections.Counter();costs=collections.Counter()
 for a,b in itertools.combinations(range(20),2):
  keep=tuple(i for i in range(20) if i not in (a,b));H=hit(keep);cost=36+len(H)
  score=counts[1<<a]+counts[1<<b]+counts[(1<<a)|(1<<b)]
  hist[score]+=1;costs[cost]+=1
  if best is None or (score,cost,a,b)<best[0]:best=((score,cost,a,b),keep,H)
 (score,cost,a,b),keep,H=best;g,out=build(keep,H)
 assert sum(ev(g,out,x)!=bool(r) for x,r in enumerate(rows))==score and len(g)==cost
 (w/'near.json').write_text(json.dumps(dict(gates=g,out=out,omitted=[a,b],wrong=score)))
 print('two-omission counts',sorted(hist.items()),'costs',sorted(costs.items()),'best',best[0],flush=True)
