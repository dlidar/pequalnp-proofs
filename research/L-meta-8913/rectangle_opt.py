"""Optimize a cover of the 52 positive flags using rectangles safe on the six negative rows."""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csc_matrix
from merged_stars import rows,edges
W=Path(__file__).resolve().parent
design=json.loads((W/'design.json').read_text())
def projected(p,l):
    pts=ls=mask=0
    for k,(i,j) in enumerate(edges):
        if p>>i&1 and l>>j&1:
            pts|=1<<i;ls|=1<<j;mask|=1<<k
    return mask,pts,ls
items={}
for p in range(1,1<<13):
    allow=(1<<13)-1
    support=0
    for i in range(13):
        if p>>i&1:support|=rows[i]
    for P,L in design:
        if P&p:allow&=~L
    allow&=support
    l=allow
    while l:
        mask,ps,ls=projected(p,l)
        if mask:items[mask]=(ps,ls)
        l=(l-1)&allow
for p in range(13):
    if all(not(P>>p&1) for P,L in design):
        items[projected(1<<p,8191)[0]]=(1<<p,0)
for l in range(13):
    if all(not(L>>l&1) for P,L in design):
        items[projected(8191,1<<l)[0]]=(0,1<<l)
m=list(items)
a=csc_matrix([[bool(mask>>i&1) for mask in m] for i in range(52)],dtype=float)
c=np.array([p.bit_count()+l.bit_count() for p,l in items.values()],dtype=float)
res=milp(c,integrality=np.ones(len(c)),bounds=Bounds(0,1),constraints=LinearConstraint(a,1,np.inf),
         options={'time_limit':40,'mip_rel_gap':0})
assert res.x is not None
chosen=[items[mask] for mask,v in zip(m,res.x) if v>.5]
print('Solver status',res.status,'feasible gates',sum(p.bit_count()+l.bit_count() for p,l in chosen)-1,
      'floating dual bound',res.mip_dual_bound,flush=True)
flags=[]
for p,l in chosen:
    flags.append(([i for i in range(13) if p>>i&1],[j for j in range(13) if l>>j&1]))
(W/'optimal-blocks.json').write_text(json.dumps(flags))
