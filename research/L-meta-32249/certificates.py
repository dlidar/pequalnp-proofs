"""Find integer leaf-rectangle certificates on the minimal encoded positives and maximal negatives."""
from labels import *
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix
from math import gcd
from functools import reduce
def rectangles(P,B,h):
    grid=np.arange(len(P)*len(B)).reshape((len(P),len(B)));groups=[]
    for sig in raw+[~h]:
        box=grid[np.ix_([i for i,x in enumerate(P) if (sig>>x)&1],[j for j,x in enumerate(B) if not (sig>>x)&1])]
        if not box.size:continue
        if len(box)>box.shape[1]:box=box.T
        subs=((np.arange(1,1<<len(box))[:,None]>>np.arange(len(box)))&1)
        groups.append((box,subs))
    return groups
def solve(h,goal):
    P,B=lift(h);groups=rectangles(P,B,h);size=len(P)*len(B)
    cuts={tuple(sorted(box.ravel())) for box,_ in groups}
    for it in range(300):
        rows=[];cols=[]
        for r,c in enumerate(cuts):rows.extend([r]*len(c));cols.extend(c)
        A=csr_matrix((np.ones(len(rows)),(rows,cols)),shape=(len(cuts),size))
        ans=linprog(-np.ones(size),A_ub=A,b_ub=np.ones(len(cuts)),bounds=(-5,1),method='highs')
        if not ans.success:raise RuntimeError(ans.message)
        w=ans.x;wi=np.rint(w*1200).astype(np.int64)
        cap=max(int(np.maximum(0,S@wi[box]).sum(axis=1).max()) for box,S in groups);total=int(wi.sum())
        if cap>0 and total>(goal-1)*cap or it==299:break
        new=set()
        for box,S in groups:
            val=S@w[box];prices=np.maximum(val,0).sum(axis=1)
            order=np.argsort(-prices)
            for q in order[:12]:
                if prices[q]<1.0000001:break
                new.add(tuple(sorted(box[np.ix_(S[q].astype(bool),val[q]>1e-9)].ravel())))
        new-=cuts
        if not new:break
        cuts|=new
    g=reduce(gcd,wi);g=max(g,1)
    return dict(P=P,N=B,weights=(wi.reshape(len(P),len(B))//g).tolist(),total=total//g,cap=cap//g,bound=(total+cap-1)//cap)
if __name__=='__main__':
    output=p/'weights-32249.json';allcert=json.loads(output.read_text()) if output.exists() else {}
    for k,op,i,j,h in cases:
        key=hex(h)
        if key in allcert:continue
        z=solve(h,15 if k==1 else 14);allcert[key]=z
        tmp=output.with_suffix('.tmp');tmp.write_text(json.dumps(allcert));tmp.replace(output)
        print(op,i,j,'cert',z['bound'],flush=True)
