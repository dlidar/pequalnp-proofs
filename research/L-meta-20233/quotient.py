"""Search for circuits with an OR of conjunctions after merging compatible row/column pairs."""
from pathlib import Path
import json,sys,itertools
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix
import numpy as np
d=Path(__file__).parent
m=14466700110149527140
def solve(p,seconds):
 col=dict((j,i) for i,j in p)
 vertices=sorted({*range(8),*(col.get(j,8+j) for j in range(8))})
 codes=[(1<<vertices.index(i)) | (1<<vertices.index(col.get(j,8+j))) for i in range(8) for j in range(8)]
 groups={}
 for S in range(1,1<<len(vertices)):
  groups[S]=sum(1<<i for i,x in enumerate(codes) if x&S)
 def subs(s):
  x=s
  while x:yield x;x=(x-1)&s
 singles=[1<<j for j in range(len(vertices))]
 terms=[]
 for a,f in groups.items():
  eligible=sum(v for v in singles if not (a&v or (f&groups[v]&~m)))
  for b in subs(eligible):
   if b<=a:continue
   t=f&groups[b]
   if not t:continue
   if any((groups.get(a^v,0)&groups[b])==t for v in singles if a&v):continue
   if any((groups.get(b^v,0)&f)==t for v in singles if b&v):continue
   terms.append((a,b,t))
 gs=sorted({s for a,b,_ in terms for x in (a,b) for s in subs(x) if s.bit_count()>1})
 ids={g:len(terms)+i for i,g in enumerate(gs)}
 cost=[2]*len(terms)+[1]*len(gs);rows=[];low=[]
 def condition(row,v):rows.append(row);low.append(v)
 for i in range(64):
  if m>>i&1:condition({j:1 for j,(_,_,t) in enumerate(terms) if t>>i&1},1)
 for i,(a,b,t) in enumerate(terms):
  for x in (a,b):
   if x in ids:condition({i:-1,ids[x]:1},0)
 options={}
 for s in gs:
  if s.bit_count()==2:continue
  opts=[]
  for a in subs(s):
   b=s^a
   if a>=b:continue
   if a in ids and b in ids:
    j=len(cost);cost.append(0)
    condition({j:-1,ids[a]:1},0);condition({j:-1,ids[b]:1},0)
   elif b in ids:j=ids[b]
   else:j=ids[a]
   opts.append(j)
  condition({ids[s]:-1,**{j:1 for j in opts}},0)
 ijv=[(i,j,v) for i,row in enumerate(rows) for j,v in row.items()]
 I,J,V=zip(*ijv);A=coo_matrix((V,(I,J)),shape=(len(rows),len(cost))).tocsc()
 res=milp(cost,integrality=np.ones(len(cost)),bounds=Bounds(0,1),constraints=LinearConstraint(A,low,np.inf),options={'time_limit':seconds})
 if res.x is None:return
 out=[]
 def gate(op,a,b):
  out.append([op,a,b]);return 15+len(out)
 ws={1<<k:v for k,v in enumerate(vertices)}
 for i,j in p:ws[1<<vertices.index(i)]=gate('or',i,j+8)
 for s in sorted(gs,key=int.bit_count):
  if res.x[ids[s]]<.5:continue
  a=next(a for a in subs(s) if a in ws and s^a in ws);ws[s]=gate('or',ws[a],ws[s^a])
 outputs=[gate('and',ws[a],ws[b]) for i,(a,b,t) in enumerate(terms) if res.x[i]>.5]
 root=outputs[0]
 for x in outputs[1:]:root=gate('or',root,x)
 # Omit any preprocessing gates outside the output cone.
 needed={root}
 for j in reversed(range(len(out))):
  if j+16 in needed:needed.update(out[j][1:])
 ids={j:j for j in range(16)};pruned=[]
 for j,(op,a,b) in enumerate(out):
  if j+16 in needed:ids[j+16]=16+len(pruned);pruned.append([op,ids[a],ids[b]])
 for j in range(64):
  tr=[int(k in (j//8,8+j%8)) for k in range(16)]
  for op,a,b in pruned:tr.append(tr[a]&tr[b] if op=='and' else tr[a]|tr[b])
  assert tr[-1]==m>>j&1
 best=d/'quotient-best.json'
 if not best.exists() or len(pruned)<len(json.loads(best.read_text())):
  best.write_text(json.dumps(pruned));print('improved',len(pruned),'from',p,'terms',len(terms),'dual',res.mip_dual_bound,flush=True)
  if len(pruned)<=23:(d/'quotient-witness.json').write_text(json.dumps(pruned))
if __name__=='__main__':
 import fcntl
 lk=(d/'research.lock').open('a');fcntl.flock(lk,fcntl.LOCK_EX|fcntl.LOCK_NB)
 best=json.loads((d/'matching-profile.json').read_text())['maximum_matchings'][0]
 ps=[best]+list(itertools.combinations(best,5))
 for p in ps:
  if (d/'stop').exists() or (d/'lost').exists() or (d/'quotient-witness.json').exists():break
  solve(p,45)
