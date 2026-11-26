"""Enumerate disjoint row-column OR signals and test every positive/negative collision."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
m=14466700110149527140
A=lambda i,j:m>>(8*i+j)&1
profiles=Counter();maxima=[];best=0;families=[]
def visit(start,assigned,cols):
 global best,maxima
 n=len(assigned);profiles[n]+=1;families.append(assigned)
 if n>best:best=n;maxima=[]
 if n==best:maxima.append(assigned)
 for i in range(start,8):
  for j in range(8):
   if j in cols or A(i,j) or any(A(i,y)!=A(x,j) for x,y in assigned):continue
   visit(i+1,assigned+[(i,j)],cols|{j})
visit(0,[],set())
print('counts',dict(profiles),'max',best,flush=True)
def rows(p):
 code=list(range(16))
 for x,y in p:code[y+8]=x
 return [{code[i],code[8+j]} for i in range(8) for j in range(8)]
def monotone(p):
 s=rows(p)
 return not any(s[i]<=s[j] for i in range(64) if m>>i&1 for j in range(64) if not(m>>j&1))
# Larger signals have two labels. Singletons only occur at matched diagonal nonedges.
# Positive two-label codes cannot be subsets of singleton codes.
assert all(monotone(p) for p in families)
allcells=[(i,j) for i in range(8) for j in range(8)]
for i,j in allcells:
 assert monotone([(i,j)]) == (not A(i,j))
for (i,j),(x,y) in combinations(allcells,2):
 if i!=x and j!=y:
  assert monotone([(i,j),(x,y)]) == (not A(i,j) and not A(x,y) and A(i,y)==A(x,j))
def independent(p):
 ws=rows(p);es=set(tuple(sorted(t)) for i,t in enumerate(ws) if m>>i&1)
 labels=sorted(set().union(*ws))
 for k in range(len(labels)+1):
  for c in combinations(labels,k):
   if all(any(x in c for x in e) for e in es):return len(es),c
costs=[]
for p in maxima:
 e,c=independent(p);costs.append((len(p)+e+len(c)-1,p,c,e))
print('maximal-size quotient star optimum',min(costs),flush=True)
(Path(__file__).parent/'matching-profile.json').write_text(json.dumps({'counts':dict(profiles),'maximum':best,'maximum_matchings':maxima,'star':min(costs)}))
