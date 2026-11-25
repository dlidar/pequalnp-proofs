"""Independent Hamming distances from full 2^24-bit truth tables."""
from itertools import combinations
from pathlib import Path
import re
from collections import Counter
text=(Path(__file__).parent/'Reference.lean').read_text().split('def exactCircuitFn')[1].split('theorem')[0]
edges=[tuple(map(int,g)) for g in re.findall(r'x (\d+) && x (\d+)',text)]
def variable(i):
 b=(bytes([[170,204,240][i]]) if i<3 else bytes(1<<(i-3))+b'\xff'*(1<<(i-3)))
 return int.from_bytes(b*((1<<21)//len(b)),'little')
inputs=list(map(variable,range(24)))
p=[0]
for a,b in edges:p.append(p[-1]|(inputs[a]&inputs[b]))
target=p[-1];suffix=0;h=Counter(); bypair={}
for k in reversed(range(len(edges))):
 a,b=edges[k];difference=(target^(p[k]|suffix)).bit_count()
 bypair[a,b]=difference;h['delete',difference]+=1;suffix|=inputs[a]&inputs[b]
for a,b in combinations(range(24),2):
 if (a,b) not in bypair:
  difference=((inputs[a]&inputs[b])&~target).bit_count();bypair[a,b]=difference;h['add',difference]+=1
print('positive inputs',target.bit_count(),'histogram',sorted(h.items()))
assert bypair[2,13]==1440 and min(bypair.values())==599 and len(bypair)==276
