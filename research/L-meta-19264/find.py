from itertools import combinations
from functools import lru_cache
raw=[sum(1<<j for j in range(16) if i in (j//4,j%4+4)) for i in range(8)]; goal=5087;ALL=65535
@lru_cache(None)
def distinguish(s):
 parts={ALL}
 for x in s:parts={w for p in parts for w in (p&x,p&~x) if w}
 return all(not(p&goal) or not(p&~goal) for p in parts)
@lru_cache(None)
def search(s,k):
 if goal in s:return []
 if len(s)>k+1 or not k or not distinguish(s):return None
 for i,a in enumerate(s):
  base=s[:i]+s[i+1:];ops=[('not',a,ALL^a,base)]
  for j,b in enumerate(base):
   rest=base[:j]+base[j+1:]
   for w in (b&a,b|a):
    if w in (a,b):continue
    for keep in [(),(a,),(b,),(a,b)]:
     if len(rest)+len(keep)>=k:continue
     ops.append(('and' if w==a&b else 'or',b,w,rest+keep))
  for op,b,z,rem in ops:
   for carry in ([(),(a,)] if op=='not' else [()]):
    t=tuple(sorted(set(rem+carry+(z,))))
    r=search(t,k-1)
    if r!=None:return [(op,a,b,z)]+r
for n in range(1,7):
 for s in combinations(raw,n):
  h=search(tuple(sorted(s)),5)
  if h!=None:
   ws=raw[:];gs=[]
   for op,a,b,z in h:gs.append((op,ws.index(a),ws.index(b)));ws.append(z)
   print(gs,ws.index(goal),flush=True);quit()
print('none',search.cache_info())
