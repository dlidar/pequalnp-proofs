from boxes import *
from scipy.sparse import hstack,vstack,eye,csr_matrix
# Include coverage slack for each positive input and forbid false positives.
B=hstack([A.tocsr(),vstack([eye(len(edges)),csr_matrix((len(C)-len(edges),len(edges)))])]).tocsr()
tokens=np.r_[[2]*n,[1]*len(groups),[0]*len(edges)]
cost=np.r_[[0]*N,[100]*len(edges)]+tokens
res=milp(cost,integrality=np.ones(B.shape[1]),bounds=Bounds(0,1),constraints=[LinearConstraint(B,lb,np.inf),LinearConstraint(tokens,0,24)])
assert res.success
sel=[b for j,b in enumerate(boxes) if res.x[j]>0.5]
gs.clear();ws={(k,1<<i):k*8+i for k in (0,1) for i in range(8)}
for k,v in sorted(groups,key=lambda t:t[1].bit_count()):
 if res.x[G[k,v]]<0.5:continue
 a=next(t for t in sub(v) if t.bit_count()==v.bit_count()-1 and (k,t) in ws)
 ws[k,v]=gate('or',ws[k,a],ws[k,v^a])
outs=[gate('and',ws[0,a],ws[1,b]) for a,b in sel];out=outs[0]
for x in outs[1:]:out=gate('or',out,x)
K=0
for r in range(64):
 vals=[j in (r//8,8+r%8) for j in range(16)]
 for op,a,b in gs:vals.append((vals[a]&vals[b]) if op=='and' else (vals[a]|vals[b]))
 K |= vals[-1]<<r
print('approx',len(gs),'missing',[(r//8,r%8) for r in range(64) if (m&~K)>>r&1],'extra',K&~m)
(d/'near.json').write_text(json.dumps({'gates':gs,'mask':K}))
