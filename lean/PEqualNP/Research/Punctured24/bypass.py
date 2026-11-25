"""Check a deletion and one arbitrary gate replacement in either canonical
55-gate circuit. A deletion can bypass to any earlier wire, including an
unrelated input. The final output may be redirected by deleting its gate.
Controls verify that the filter recognizes an artificial single-gate repair.
"""
import itertools
from rewire import E,mask,inputs,evaluate,ev
def full(dual):
 w=[]
 def fold(op, wires):
  v,*rest=wires
  for b in rest:
   w.append((op,v,b));v=len(w)+23
  return v
 es=[(b,a) if dual else (a,b) for a,b in E];s=[]
 for i in sorted({a for a,b in es}):
  r=fold('or',sorted(b for a,b in es if a==i))
  s.append(fold('and',[i,r]))
 fold('or',s);assert len(w)==55
 return w
target=0
for a,b in E:target|=inputs[a]&inputs[b]
def repair(g,output):
 wires=evaluate(g,inputs,mask)
 if wires[output]==target:return (-1,'identity',0,0)
 for k in reversed(range(min(len(g),output-23))):
  low,high=[evaluate(g,inputs,mask,(k,v))[output] for v in (0,mask)]
  yes=target & ~low; no=high & ~target
  if yes & ~high or low & ~target:continue
  if yes==0 or no==0:return (k,'constant',int(no==0),0)
  # Binary AND operands must both contain every required positive and OR
  # operands must both avoid every forbidden positive.
  block=wires[:k+24]
  for op in ('and','or'):
   cand=[(a,v) for a,v in enumerate(block) if (v & yes==yes if op=='and' else not v & no)]
   for idx,(a,v) in enumerate(cand):
    for b,u in cand[idx:]:
     if (not (v&u)&no if op=='and' else (v|u)&yes==yes):return k,op,a,b
  for a,v in enumerate(block):
   if not v & yes and (v & no)==no:return k,'not',a,a
 return None
if __name__=='__main__':
 total=0
 for dual in (False,True):
  g=full(dual);out=78
  assert evaluate(g,inputs,mask)[out]==target
  altered=g.copy();altered[-1]=('and',0,1)
  assert repair(altered,out) is not None
  for k in range(55):
   old=k+24
   for src in range(old):
    def new(i):return src if i==old else i-int(i>old)
    h=[(op,new(a),new(b)) for idx,(op,a,b) in enumerate(g) if idx!=k]
    r=repair(h,new(out));total+=1
    if r is not None:print('candidate',dual,k,src,r,flush=True)
  print('completed orientation',dual,'cumulative bypasses',total,flush=True)
