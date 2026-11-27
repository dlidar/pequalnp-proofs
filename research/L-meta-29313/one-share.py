"""Screen all possible boundary tables of the only shared monotone wire."""
from labels import *
from collections import Counter
import subprocess
B=E+N;mask=(1<<19)-1
def gate_limit(h):
 a=h&8191;b=h>>13
 # Prefix formula must separate P1 from N0. Encoding C has unit cost for empty rectangles.
 prefix=C[a*64+63-b]-1
 pin=max(C[(8191^a)*64+63] if a!=8191 else 0, C[8191*64+b] if b else 0)
 return prefix,12-pin
limits=[gate_limit(h) for h in range(1<<19)]
K=max(upper for lower,upper in limits if lower<=upper)
assert K==7
base=[sum(((x>>i)&1)<<k for k,x in enumerate(B)) for i in range(8)]
levels=[sorted(set(base))]; seen=set(base)
for cost in range(1,K+1):
 new=set()
 for k in range((cost-1)//2+1):
  for a in levels[k]:
   for b in levels[cost-1-k]:new.add(a&b);new.add(a|b)
 new-=seen;seen|=new;levels.append(sorted(new))
viable=[(c,h) for c in range(1,K+1) for h in levels[c] if c<=limits[h][1]]
print('widths',list(map(len,levels)),'viable',Counter(c for c,h in viable),flush=True)
sol=subprocess.Popen([p/'smalldec'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
stats=Counter();hits=[]
for c,h in viable:
 rows=[x+256*((h>>i)&1) for i,x in enumerate(B)]
 sol.stdin.write(' '.join(map(str,[13,6]+rows))+'\n');sol.stdin.flush()
 d=int(sol.stdout.readline());stats[c+d-1]+=1
 if c+d-1<=13:hits.append([c,h,d])
sol.stdin.close();sol.wait()
print('total gates among viable',stats,'hits',hits,flush=True)
(p/'one-share.json').write_text(json.dumps(dict(widths=list(map(len,levels)),candidates=viable,counts=dict(stats),hits=hits)))
