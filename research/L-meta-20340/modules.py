from pathlib import Path
import json
from collections import Counter
d=Path(__file__).parent;m=1885146376704737940
row=[(1<<(v//8))|(1<<(8+v%8)) for v in range(64)]
pairs=[(p,n,row[p]&~row[n]) for p in range(64) if m>>p&1 for n in range(64) if not (m>>n&1)]
rules={}
for a,b,x in pairs:
 for c,h,y in pairs:
  lo=x|y;out=row[a]&~row[h]
  if not lo&out:rules.setdefault((lo,out),(a,b,c,h))
# Test all masks in parallel with Python integers.
allsets=(1<<65536)-1
bit=[int.from_bytes(bytes(sum(((8*t+j)>>i&1)<<j for j in range(8)) for t in range(8192)),'little') for i in range(16)]
left=allsets;cert=[]
while left:
 best=0;bn=0
 if not cert:
  ban={}
  for u,v in rules:
   s=allsets
   for i in range(16):
    if u>>i&1:s&=bit[i]
    if v>>i&1:s&=~bit[i]
   ban[u,v]=s
 for key,z in ban.items():
  score=(z&left).bit_count()
  if score>bn:bn=score;best=key
 if not bn:break
 left &= ~ban[best];cert.append([*best,*rules[best]])
good=[i for i in range(65536) if left>>i&1]
cache={}
for s in good:
 need=[(p,n) for p,n,k in pairs if k&~s==0]
 val=sum(1<<j for j in range(64) if any(row[p]&s&~row[j]==0 for p,n in need))
 assert all((val>>p&1) and not (val>>n&1) for p,n in need)
 cache[s]=val
print('good',len(good),Counter(x.bit_count() for x in good),'intervals',len(cert),flush=True)
print('nontrivial',[(hex(s),hex(v)) for s,v in cache.items() if 1<s.bit_count()<16],flush=True)
(d/'modules.json').write_text(json.dumps({'cache':cache,'forbidden':cert}))
