"""Search every single gate replacement in the 88 canonical 54-gate near circuits.
Use all Hamming weight <=2 assignments as a necessary filter. A survivor is a candidate requiring full validation.
"""
from pathlib import Path
import json,re,itertools
root=Path(__file__).parent
E=[tuple(map(int,p)) for p in re.findall(r'x (\d+) && x (\d+)',(root/'Reference.lean').read_text().split('def exactCircuitFn')[1].split('theorem')[0])]
tests=[0]+[1<<a for a in range(24)]+[(1<<a)|(1<<b) for a,b in itertools.combinations(range(24),2)]
mask=(1<<len(tests))-1
inputs=[sum(1<<j for j,x in enumerate(tests) if x>>v&1) for v in range(24)]
def ev(op,x,y,M):return (x&y) if op=='and' else (x|y) if op=='or' else M^x
def evaluate(g,inp,M,fixed=None):
 w=inp.copy()
 for k,(op,a,b) in enumerate(g):
  w.append(fixed[1] if fixed and k==fixed[0] else ev(op,w[a],w[b],M))
 return w
def circ(edges):
 g=[]
 def gate(op,a,b):g.append((op,a,b));return 23+len(g)
 def fold(op,ls):
  a,*xs=ls
  for b in xs:a=gate(op,a,b)
  return a
 stars=[gate('and',i,fold('or',sorted(b for a,b in edges if a==i))) for i in sorted({a for a,b in edges})]
 fold('or',stars);assert len(g)==54
 return g
def solve():
 target=0
 for a,b in E: target|=inputs[a]&inputs[b]
 tried=0;survivors=0
 for excluded,dual in itertools.product(E,[False,True]):
  g=circ([(b,a) if dual else (a,b) for a,b in E if (a,b)!=excluded])
  wires=evaluate(g,inputs,mask)
  for k in range(len(g)):
   low,high=[evaluate(g,inputs,mask,(k,v))[-1] for v in (0,mask)]
   required=target & ~low;forbidden=high & ~target
   if required & ~high or low & ~target:continue
   def valid(v):return (v & required)==required and not (v & forbidden)
   for a in range(k+24):
    for b in range(a,k+24):
     for op in ('and','or','not') if a==b else ('and','or'):
      tried+=1
      if valid(ev(op,wires[a],wires[b],mask)):
       survivors+=1;yield excluded,dual,k,op,a,b
   for const in (0,mask):
    if valid(const):survivors+=1;yield excluded,dual,k,'constant',bool(const)
 print('88 circuits; single replacements surviving all 301 tests:',survivors,'candidate operations tested after sensitivity pruning:',tried,flush=True)
if __name__=='__main__':
 for item in solve():print(item,flush=True)
