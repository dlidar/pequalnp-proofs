"""Find a sharp independent set and produce a branching certificate for its upper bound."""
from functools import lru_cache
from pathlib import Path
V=range(24)
E=sorted(set(tuple(sorted(e)) for i in V for e in [(i,(i+1)%24),(i,(i+[12,7,-7][i%3])%24)]))
N=[sum(1<<j for j in V if tuple(sorted((i,j))) in E) for i in V]
allv=(1<<24)-1
@lru_cache(None)
def best(s):
 if not s:return 0
 v=max((i for i in V if s>>i&1),key=lambda i:(s&N[i]).bit_count());t=s^(1<<v)
 return max(best(t),best(t&~N[v])|(1<<v),key=int.bit_count)
def matching(s):
 pairs=[]
 while s:
  v=min((i for i in V if s>>i&1),key=lambda i:((s&N[i]).bit_count() or 25))
  s^=1<<v
  if s&N[v]:
   u=min((i for i in V if s&N[v]>>0 and s>>i&1 and N[v]>>i&1),key=lambda i:(s&N[i]).bit_count())
   s^=1<<u;pairs.append((v,u))
 return pairs
nodes={}
def branch(s,k):
 if (s,k) in nodes:return
 pairs=matching(s)
 if s.bit_count()-len(pairs)<=k:nodes[s,k]=pairs;return
 v=max((i for i in V if s>>i&1),key=lambda i:(s&N[i]).bit_count())
 t=s^(1<<v)
 branch(t,k);branch(t&~N[v],k-1);nodes[s,k]=v
if __name__=='__main__':
 i=best(allv);branch(allv,i.bit_count());print(len(E),i.bit_count(),hex(i),len(nodes))
