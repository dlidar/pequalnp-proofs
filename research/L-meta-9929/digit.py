from itertools import combinations,product
def grid(n,f):
 return sum(bool(f(*[(i>>j)&1 for j in range(n)]))<<i for i in range(1<<n))
def nxt(state,mask):
 return {mask ^ x for x in state}|{x&y for x,y in combinations(state,2)}|{x|y for x,y in combinations(state,2)}
def levels(n,depth):
 m=(1<<(1<<n))-1
 sources=frozenset(grid(n,lambda *a:a[j]) for j in range(n))
 states={sources};cost={v:0 for v in sources}; cost[0]=cost[m]=0
 for k in range(1,depth+1):
  follow=set()
  for s in states:
   for t in nxt(s,m)-s-{0,m}:
    cost.setdefault(t,k)
    if k<depth:follow.add(s|{t})
  states=follow
 return cost
if __name__=='__main__':
 cost=levels(3,5)
 for a,b in product(range(2),repeat=2):
  t=grid(3,lambda c,x,y: (x+(1-y)+(c^a)>=2)^b)
  print(a,b,t,cost.get(t))
 for sz in range(1,6):
  hist={}
  for S in combinations(range(6),sz):
   axes=[j for j in range(6) if j not in S]
   def expand(index,ii):return sum((index>>k&1)<<j for k,j in enumerate(ii))
   rows=set()
   for i in range(1<<sz):
    tt=0
    for j in range(1<<len(axes)):
     w=expand(i,S)|expand(j,axes);tt|=int((w&7)>(w>>3))<<j
    rows.add(tt)
   hist.setdefault(len(rows),[]).append(S)
  print(sz,{k:len(v) for k,v in sorted(hist.items())},'admit',hist.get(2))
