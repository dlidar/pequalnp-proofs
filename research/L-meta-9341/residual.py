from rects import *
from affine import actions
from fractions import Fraction
from collections import Counter
import numpy as np
from scipy.optimize import linprog
def data():
 cells,opts=quotient(3)
 orbits=[[( (i+h)%21,(j+h)%21) for h in range(0,21,3)] for i,j in cells]
 reps=[r for r in boxes() if r==orbit(r,3)[0]]
 A=np.array([[sum(bool(a>>i&1 and b>>j&1) for i,j in o) for o in orbits] for a,b in reps],dtype=np.int32)
 perms=set()
 for act,r,c in actions():
  perms.add(tuple(cells.index((r[i]%3,(c[j]-(r[i]-r[i]%3))%21)) for i,j in cells))
 todo=set(opts);families=[]
 for m in sorted(opts):
  if m not in todo:continue
  indices=[k for k in range(48) if m>>k&1]
  fam={sum(1<<p[k] for k in indices) for p in perms}
  assert fam<=opts.keys()
  todo-=fam;families.append((m,len(fam)))
 assert not todo and sum(n for m,n in families)==len(opts)
 return cells,opts,A,families
def main():
 cells,opts,A,families=data();res=[];print('families',len(families),flush=True)
 for m,mult in families:
  inds=[i for i in range(48) if not m>>i&1]
  B=A[:,inds];r=linprog(-7*np.ones(len(inds)),A_ub=B,b_ub=np.ones(len(B)),bounds=(0,None),method='highs')
  assert r.success
  from math import lcm,gcd
  # Compress rational dual weights when their common denominator is small.
  fr=[Fraction(float(x)).limit_denominator(3000) for x in r.x]
  den=lcm(*(x.denominator for x in fr))
  w=[round(float(x)*1000000) for x in r.x] if den>100000000 else [int(x*den) for x in fr]
  w=np.array(w,dtype=np.int64);cap=int((B@w).max());total=7*int(w.sum())
  res.append([m,mult,w.tolist(),cap,total])
 low=min(Fraction(v[4],v[3]) for v in res);print('weakest certified ratio',low,'thresholds',sorted(Counter([(t-1)//c+1 for m,n,w,c,t in res]).items()),flush=True)
 print('min attained on',sum(n for m,n,w,c,t in res if Fraction(t,c)==low),'quotient footprints')
 (d/'all-residual-duals.json').write_text(json.dumps(res))
if __name__=='__main__':main()
