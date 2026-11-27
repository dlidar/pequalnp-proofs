"""Check every single-gate substitution at fixed output and every output rewire."""
from pathlib import Path
import re
src=(Path(__file__).resolve().parent/'OneNotPartial.lean').read_text()
rows=[int(n,16) for n in re.findall(r'0x[0-9a-f]+',src.split('def targetRows')[1].split('def actualRows')[0])]
gates=[tuple(map(int,x)) for x in re.findall(r'\((\d+),(\d+),(\d+)\)',src.split('def codes')[1].split('def circuit')[0])]
assert len(rows)==32 and len(gates)==170
allbits=(1<<1024)-1
target=sum(r<<(32*i) for i,r in enumerate(rows))
raw=[sum(1<<(u*32+v) for u in range(32) for v in range(32) if k==u or k==v+32) for k in range(64)]
def replay(pos=-1,value=0):
 wires=raw[:]
 for i,(op,a,b) in enumerate(gates,64):
  wires.append(value if i==pos else wires[a]&wires[b] if op==0 else wires[a]|wires[b] if op==1 else wires[a]^allbits)
 return wires
original=replay()
initial=(original[-1]^target).bit_count()
best=1025;cnt=0
for i in range(64,len(original)):
 zero=replay(i,0)[-1];one=replay(i,allbits)[-1]
 care=zero^one;desired=(zero^target)&care;unavoidable=((zero^target)&~care).bit_count()
 alternatives=[v&care for v in original[:i]]
 def mismatch(v):return unavoidable+(desired^v).bit_count()
 local=min(mismatch(0),mismatch(care));cnt+=2
 for a,A in enumerate(alternatives):
  local=min(local,mismatch(care^A));cnt+=1
  for b in range(a+1):
   B=alternatives[b];local=min(local,mismatch(A|B),mismatch(A&B));cnt+=2
 best=min(best,local)
print('initial',initial,'single gate minimum',best,'gate replacements',cnt,'output-only minimum',min((v^target).bit_count() for v in original+[0]))
