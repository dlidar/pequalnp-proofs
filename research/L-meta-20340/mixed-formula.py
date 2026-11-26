"""Certify the minimum leaf count for a disjunction of products of two raw disjunctions."""
from fractions import Fraction
import itertools, json
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
d=Path(__file__).parent
m=1885146376704737940
edges=[i for i in range(64) if m>>i&1]
def truth(s):
 return sum(1<<j for j in range(64) if s & (1<<(j//8) | 1<<(8+j%8)))
def sub(s):
 t=s
 while t:yield t;t=(t-1)&s
def support(i,j):return i|(j<<8)
rect=[]
for a in range(1,256):
 b=255
 for i in range(8):
  if a>>i&1:b&=m>>(8*i)&255
 for t in sub(b):rect.append((a,t))
terms={}
def save(a,b):
 mask=truth(a)&truth(b)
 assert mask and not(mask&~m)
 cost=a.bit_count()+b.bit_count()
 if mask not in terms or terms[mask][0]>cost:terms[mask]=(cost,a,b)
for a,b in rect:save(a,b<<8)
for (a,b),(c,v) in itertools.combinations(rect,2):
 if a&c==0 and b&v==0:save(support(a,v),support(c,b))
ms=list(terms);cost=[terms[t][0] for t in ms]
inc=np.array([[(t>>i)&1 for i in edges] for t in ms])
lp=linprog(-np.ones(len(edges)),A_ub=inc,b_ub=cost,bounds=(0,None),method='highs')
v=[Fraction(float(x)).limit_denominator(1680) for x in lp.x]
assert all(sum(y for i,y in zip(edges,v) if t>>i&1)<=terms[t][0] for t in ms)
print('distinct terms',len(ms),'dual',str(sum(v)),'weights',list(map(str,v)),flush=True)
(d/'mixed-dual.json').write_text(json.dumps(list(map(str,v))))
# A memoized cover search compresses identical remaining edge sets and charges integer leaf cost.
from functools import lru_cache
from math import lcm
den=lcm(*(k.denominator for k in v))
counts={i:int(k*den) for i,k in zip(edges,v)}
by={i:sorted((t for t in ms if t>>i&1),key=lambda t:terms[t][0]/t.bit_count()) for i in edges}
def weight(s):return sum(counts[i] for i in edges if s>>i&1)
calls=0
@lru_cache(None)
def find(s,budget):
 global calls
 calls+=1
 if not s:return ()
 slack=budget*den-weight(s)
 if slack<0:return
 def viable(i):
  return [t for t in by[i] if terms[t][0]*den-weight(t&s)<=slack]
 chosen=None
 for i in edges:
  if s>>i&1:
   opts=viable(i)
   if not opts:return
   if chosen is None or len(opts)<len(chosen):chosen=opts
 for t in chosen:
  rest=find(s&~t,budget-terms[t][0])
  if rest is not None:return (t,)+rest
assert find(m,28) is None
w=find(m,29)
assert w is not None
witness=[terms[t] for t in w]
cover=0
for c,a,b in witness:cover|=truth(a)&truth(b)
assert cover==m and sum(x[0] for x in witness)==29
print('checked states',calls,'minimum leaves 29','terms',witness,flush=True)
(d/'mixed-cover.json').write_text(json.dumps(witness))
