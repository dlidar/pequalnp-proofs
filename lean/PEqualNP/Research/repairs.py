"""Try every single gate replacement of the 123-gate reference on necessary tests.
Each mask of available line neighbours gives one maximal independent set.
For a fixed gate, forcing its output to each constant determines exactly which
positive and negative tests constrain a replacement. All later gates are monotone.
"""
from pathlib import Path
import json,re
w=Path(__file__).parent
source=(w/'PuncturedCircuits.lean').read_text()
target=source.split('namespace Reference')[1].split('def target')[1].split('theorem correct')[0]
edges=[tuple(map(int,pair)) for pair in re.findall(r'x (\d+) && x (\d+)',target)]
assert len(edges)==104
a=source.split('namespace Approx')[1].split('theorem size_eq')[0]
gates=[(op,int(x),int(y)) for op,x,y in re.findall(r'⟨\.(or|and),\[(\d+),(\d+)\]⟩',a)]
assert len(gates)==123
rows=[sum(1<<(j-21) for i,j in edges if i==p) for p in range(21)]
ms={0}
for r in rows:ms|={m|r for m in ms}
tests=[1<<i|1<<j for i,j in edges]+[(sum(1<<i for i,r in enumerate(rows) if not r&~m)|(((1<<21)-1)^m)<<21) for m in sorted(ms)]
assert len(tests)==25029
def pack(bools):
 acc=bytearray((len(tests)+7)//8)
 for i,t in enumerate(bools):
  if t:acc[i//8]|=1<<(i%8)
 return int.from_bytes(acc,'little')
xs=[pack(t>>j&1 for t in tests) for j in range(42)]
top=(1<<len(tests))-1; wanted=(1<<len(edges))-1
def extend(v,at=0):
 for op,i,j in gates[at:]:v.append(v[i]&v[j] if op=='and' else v[i]|v[j])
 return v
v=extend(xs[:])
assert (wanted^v[-1]).bit_count()==1
count=0; best=1; survivors=[]
for g,(op,a,b) in enumerate(gates):
 idx=42+g
 low=extend(v[:idx]+[0],g+1)[-1];high=extend(v[:idx]+[top],g+1)[-1]
 # An intrinsic mismatch precludes any repair at this gate.
 candidates=(idx+2)*(idx+3)+(idx+2)
 count+=candidates
 if low&~wanted or wanted&~high:continue
 pos=wanted&~low;neg=high&~wanted
 wires=v[:idx]+[0,top]
 projections=[(z&pos,z&neg) for z in wires]
 for i,(pi,ni) in enumerate(projections):
  if pi==0 and ni==neg:survivors.append((g,'not',i))
  for j in range(i+1):
   pj,nj=projections[j]
   if pi==pos and pj==pos and ni&nj==0:survivors.append((g,'and',i,j))
   if ni==0 and nj==0 and pi|pj==pos:survivors.append((g,'or',i,j))
print('gates',len(gates),'necessary rows',len(tests),'replacements including constants, duplicate operands and original gate',count,'survivors',survivors,flush=True)
(w/'survivors.json').write_text(json.dumps(survivors))
