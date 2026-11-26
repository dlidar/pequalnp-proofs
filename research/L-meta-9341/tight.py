from rects import *
from collections import Counter
def tight_cases():
 _,opts=quotient(3); cells=[(i,j) for i in range(3) for j in range(21) if not rows[i]>>j&1]
 for m,n,weights,cap,total in json.loads((d/'all-residual-duals.json').read_text()):
  if total>8*cap:continue
  cc=[(i,j) for k,(i,j) in enumerate(cells) if not m>>k&1]
  targets=[((i+h)%21,(j+h)%21,w) for (i,j),w in zip(cc,weights) for h in range(0,21,3)]
  cov={};bs=boxes()
  for r in bs:
   a,b=r;mask=sum(1<<k for k,(i,j,_) in enumerate(targets) if a>>i&1 and b>>j&1)
   score=sum(w for k,(_,_,w) in enumerate(targets) if mask>>k&1)
   if score+7*cap>=total:cov[mask]=r
  yield m,cap,total,targets,cov,opts[m]
def tree(cap,Q,targets,cov):
 masks=list(cov)
 lists=[tuple(m for m in masks if m>>i&1) for i in range(len(targets))]
 layers=[sum(1<<i for i,(a,b,w) in enumerate(targets) if w>=s) for s in range(1,max(w for a,b,w in targets)+1)]
 def wt(mask):return sum((b&mask).bit_count() for b in layers)
 nodes=Counter();trace=[]
 def dfs(rem,k):
  nodes[k]+=1
  if not rem:return []
  if not k:return None
  budget=wt(rem)-(k-1)*cap
  ix=sorted((i for i in range(len(targets)) if rem>>i&1),key=lambda i:len(lists[i]))
  best=None;bestcell=None
  for cell in ix:
   possible=[]
   for m in lists[cell]:
    if wt(rem&m)>=budget:
     possible.append(m)
     if best is not None and len(possible)>=len(best):break
   if not possible:
    trace.append(cell);return None
   if best is None or len(possible)<len(best):best=possible;bestcell=cell
  trace.append(bestcell)
  for m in sorted(best):
   suffix=dfs(rem&~m,k-1)
   if suffix is not None:return [m]+suffix
  return None
 rs=dfs((1<<len(targets))-1,8)
 return rs,nodes,trace
if __name__=='__main__':
 for m,c,t,targets,cov,seed in tight_cases():
  print(hex(m),'eligible',len(cov),flush=True)
  solution,nodes,trace=tree(c,t,targets,cov)
  print(hex(m),'solution',solution is not None,'nodes',sorted(nodes.items()),flush=True)
  if solution is None:(d/f'branch-cells-{m}.json').write_text(json.dumps(trace))
  if solution:
   rect=seed+[cov[u] for u in solution]
   assert validate(rect)==0
   (d/f'plus-eight-{m}.json').write_text(json.dumps(rect))
