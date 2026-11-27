"""Exact monotone one-way widths for all vertex cuts of the graph."""
from pathlib import Path
import json,itertools
p=Path(__file__).resolve().parent
edges=json.loads((p/'bounds.json').read_text())['positive']
def fun(s):return any(s&e==e for e in edges)
def masks(t):return [a for a in range(256) if a&t==a]
def problem(cut):
 inputs=masks(cut);rest=255^cut
 critical=set()
 for t in [0]+[1<<j for j in range(8) if rest>>j&1]:
  yes=[a for a in inputs if fun(a|t)]
  no=[a for a in inputs if not fun(a|t)]
  ps=[a for a in yes if not any(x!=a and x&a==x for x in yes)]
  ns=[a for a in no if not any(x!=a and x&a==a for x in no)]
  critical.update(itertools.product(ps,ns))
 pts=sorted(critical)
 adj=[sum(1<<j for j,(c,d) in enumerate(pts) if a&d==a or c&b==c) for a,b in pts]
 return pts,adj
def bits(x):
 while x:
  y=x&-x;yield y.bit_length()-1;x-=y
def clique(adj,k):
 def extend(vs,ls):
  if len(ls)==k:return ls
  while vs.bit_count()>=k-len(ls):
   j=next(bits(vs));vs^=1<<j
   r=extend(vs&adj[j],ls+[j])
   if r:return r
 return extend((1<<len(adj))-1,[])
def color(adj,k):
 n=len(adj);forbid=[0]*n;cols=[-1]*n
 def go(left,used):
  if not left:return cols[:]
  j=max(bits(left),key=lambda x:(forbid[x].bit_count(),(adj[x]&left).bit_count()))
  allowed=((1<<min(k,used+1))-1)&~forbid[j]
  for c in bits(allowed):
   bit=1<<c;cols[j]=c;changed=[]
   for i in bits(adj[j]&left):
    if not forbid[i]&bit:forbid[i]|=bit;changed.append(i)
   ans=go(left^(1<<j),max(used,c+1))
   if ans:return ans
   for i in changed:forbid[i]^=bit
   cols[j]=-1
  return None
 return go((1<<n)-1,0)
def main():
 from collections import Counter
 out={};nongap=Counter()
 for t in range(1,256):
  pts,adj=problem(t);ub=min(t.bit_count(),9-t.bit_count())
  for k in range(1,ub+1):
   if clique(adj,k+1):continue
   sol=color(adj,k)
   if sol is not None:break
  assert sol is not None
  lb=clique(adj,k)
  groups=[sorted({a for (a,b),z in zip(pts,sol) if z==c}) for c in range(k)]
  out[t]={'width':k,'uppers':groups,'clique':[pts[j] for j in lb] if lb else []}
  if not lb:nongap[k]+=1
 print('cuts without matching clique',nongap)
 for b in range(1,9):print(b,Counter(x['width'] for t,x in out.items() if t.bit_count()==b))
 (p/'cutwidth.json').write_text(json.dumps(out,separators=(',',':')))
if __name__=='__main__':main()
