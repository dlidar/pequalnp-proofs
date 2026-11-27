from pathlib import Path
import json,itertools,collections
p=Path(__file__).resolve().parent
edges=json.loads((p/'bounds.json').read_text())['edges']
def graph(s):return any(s>>i&s>>j&1 for i,j in edges)
D=json.loads((p/'cutwidth.json').read_text())
T=json.loads((p/'cut-traces.json').read_text())
def incompatible(a,b):return a[0]&b[1]==a[0] or b[0]&a[1]==b[0]
def group(cl):
 assert all(incompatible(i,j) for i,j in itertools.combinations(cl,2))
nodes=0
for cut in range(1,256):
 d=D[str(cut)];k=d['width'];U=[x for x in range(256) if x&cut==x];V=[x for x in range(256) if x&cut==0]
 # Truth tables of all residual functions, indexed by external assignment.
 rows={x:sum(int(graph(x|v))<<j for j,v in enumerate(V)) for x in U}
 codes={x:sum(int(any(a&x==a for a in gen))<<i for i,gen in enumerate(d['uppers'])) for x in U}
 assert len(d['uppers'])==k
 for x,y in itertools.product(U,repeat=2):
  if x&y==x:assert codes[x]&codes[y]==codes[x]
  if codes[x]&codes[y]==codes[x]:assert rows[x]&rows[y]==rows[x]
 def pair_ok(pair):
  a,b=pair
  return a in rows and b in rows and rows[a]&~rows[b]!=0
 if d['clique']:
  cl=d['clique'];assert len(cl)==k and all(map(pair_ok,cl));group(cl)
 else:
  rec=T[str(cut)];ps=rec['pairs'];seed=rec['seed']
  assert all(map(pair_ok,ps)) and len(seed)==k-1 and len(set(seed))==k-1
  group([ps[i] for i in seed])
  def walk(assign,proof):
   global nodes
   nodes+=1;i,branches=proof;assert 0<=i<len(ps) and i not in assign
   colors=[c for c in range(k-1) if all(c!=v or not incompatible(ps[i],ps[j]) for j,v in assign.items())]
   assert len(colors)==len(branches)
   for c,z in zip(colors,branches):walk({**assign,i:c},z)
  walk({u:i for i,u in enumerate(seed)},rec['trace'])
print('255 exact cut widths;',len(T),'coloring traces;',nodes,'verified proof nodes')
for b in range(1,9):
 print(b, sorted(collections.Counter(D[str(t)]['width'] for t in range(1,256) if t.bit_count()==b).items()))
