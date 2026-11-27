"""Exact integer checks on all monochromatic one rectangles and on a fixed OR dictionary."""
from functools import cache
from itertools import combinations
from pathlib import Path
import json
p=Path(__file__).resolve().parent
data=json.loads((p/'weights.json').read_text());R=data['rows']
weights={(u,v):w for u,v,w in data['weights']}
assert all(0<=u<32 and 0<=v<32 and R[u]>>v&1 and w>0 for (u,v),w in weights.items())
# Enumerate using column neighborhoods, independently of the row-intersection generator.
rowsets={2**32-1}
for v in range(32):
 col=sum((r>>v&1)<<i for i,r in enumerate(R))
 rowsets.update(x&col for x in tuple(rowsets))
cap=0;count=0
for rs in rowsets-{0}:
 cols=2**32-1
 for u,r in enumerate(R):
  if rs>>u&1:cols&=r
 if not cols:continue
 count+=1
 cap=max(cap,sum(w for (u,v),w in weights.items() if (rs>>u)&(cols>>v)&1))
total=sum(weights.values())
assert cap==data['cap'] and total==data['total']
print('positive rectangles',count,'total',total,'cap',cap,'minimum cover at least',(total+cap-1)//cap)
terms=list(map(int,(p/'terms').read_text().split()))
data=json.loads((p/'rootprices.json').read_text())
scale=data['scale'];price={(a,b):w for a,b,w in data['prices']}
# Dictionary nodes shared by two target supports are submasks of the intersection.
D=set(terms)
for a,b in combinations(terms,2):
 s=a&b;subs=[0]
 while s:
  bit=s&-s;s-=bit;subs.extend([v|bit for v in subs])
 D.update(x for x in subs if x.bit_count()>1)
assert all(a in D and b in D and a!=b and a&b==b and w>=0 for (a,b),w in price.items())
singletons={1<<i for i in range(64)}
lb=0
for a in sorted(D):
 parts=[b for b in D|singletons if b!=a and b&a==b]
 incoming=sum(w for (_,b),w in price.items() if b==a)
 @cache
 def cost(rest):
  if rest==0:return 0
  # Pick the highest uncovered bit; any cover must hit it.
  bit=1<<(rest.bit_length()-1)
  return min(scale+price.get((a,b),0)+cost(rest&~b) for b in parts if b&bit)
 val=cost(a)-scale-incoming
 lb+=val if a in terms else min(val,0)
assert lb==data['bound']
print('reference OR preprocessing',(lb+scale-1)//scale,'total with 16 products and 15 output ORs',(lb+scale-1)//scale+31)
