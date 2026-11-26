"""Enumerate single binary gate replacements at the 63-gate reference on the posted boundary."""
from itertools import combinations, combinations_with_replacement

mask=lambda a:sum(1<<i for i in a)
lines=[{(i+t)%13 for t in (0,1,3,9)} for i in range(13)]
pos=[(1<<p)|(1<<(13+l)) for l,L in enumerate(lines) for p in sorted(L)]
neg=[mask(Q)|mask(13+l for l,L in enumerate(lines) if not L.intersection(Q)) for Q in combinations(range(13),4) if all(len(L.intersection(Q))<=2 for L in lines)]
rows=pos+neg
assert len(set(pos))==52 and len(set(neg))==234
def build(omit):
 gates=[]
 def add(op,a,b):
  a,b=sorted((a,b));gates.append((op,a,b));return len(gates)+25
 stars=[]
 for i,L in enumerate(lines):
  S=sorted(L-{0}) if omit and i==0 else sorted(L)
  t=S[0]
  for v in S[1:]:t=add(0,t,v)
  stars.append(add(1,t,13+i))
 t=stars[0]
 for v in stars[1:]:t=add(0,t,v)
 return gates
def errors(g):
 bits=[mask(t for t,r in enumerate(rows) if r>>i&1) for i in range(26)]
 for op,a,b in g:bits.append(bits[a]&bits[b] if op else bits[a]|bits[b])
 diff=bits[-1]^((1<<52)-1)
 return [i for i in range(len(rows)) if diff>>i&1]
assert errors(build(False))==[] and len(build(False))==64
ref=build(True)
assert len(ref)==63 and errors(ref)==[0]
bits=[mask(t for t,r in enumerate(rows) if r>>i&1) for i in range(26)]
for op,a,b in ref:bits.append(bits[a]&bits[b] if op else bits[a]|bits[b])
target=(1<<52)-1
best=286;count=0;optimal=0
for j,(op,a,b) in enumerate(ref):
 k=26+j
 for u,v in combinations_with_replacement(range(k),2):
  for kind,val in [(0,bits[u]|bits[v]),(1,bits[u]&bits[v])]:
   if (kind,u,v)==(op,a,b):continue
   count+=1;z=bits[:k]+[val]
   for h,x,y in ref[j+1:]:z.append(z[x]&z[y] if h else z[x]|z[y])
   err=(target^z[-1]).bit_count()
   if err<best:best=err;optimal=0
   if err==best:optimal+=1
print(count,best,optimal,flush=True)
