"""Dynamic programming on graph edges for an OR of complete bipartite products."""
import json,itertools
from pathlib import Path
p=Path(__file__).resolve().parent
edges=[(0, 3), (1, 4), (0, 5), (1, 5), (2, 5), (0, 6), (2, 6), (3, 6), (0, 7), (1, 7), (2, 7), (3, 7), (5, 7), (6, 7)]
aset={tuple(sorted(e)) for e in edges}
def target(x):return any((x>>a)&(x>>b)&1 for a,b in edges)
def witnesses():
 blocks=[]
 for colors in itertools.product(range(3),repeat=8):
    a=[i for i,c in enumerate(colors) if c==1];b=[i for i,c in enumerate(colors) if c==2]
    if not a or not b or min(a)>min(b):continue
    pairs={tuple(sorted((i,j))) for i in a for j in b}
    if pairs<=aset:blocks.append((sum(1<<edges.index(e) for e in pairs),len(a)+len(b),a,b))
 size=1<<len(edges);cost=[100]*size;prev=[None]*size;cost[0]=0
 for mask in range(size-1):
    if cost[mask]>=100:continue
    bit=(~mask)&(mask+1)
    for new,k,a,b in blocks:
        if new&bit and cost[mask]+k<cost[mask|new]:
            cost[mask|new]=cost[mask]+k;prev[mask|new]=mask,a,b
 best=cost[-1]-1
 def synth(pl):
    g=[];cache={}
    def gate(op,a,b):
        key=(op,*sorted([a,b]))
        if key not in cache:cache[key]=len(g)+8;g.append(key)
        return cache[key]
    def OR(L):
        v=L[0]
        for i in L[1:]:v=gate('or',v,i)
        return v
    OR([gate('and',OR(a),OR(b)) for a,b in pl]);return g
 res=[]
 def walk(m,pl):
    if m==size-1:
        g=synth(pl)
        if not res or len(g)<len(res):res[:]=g
        return
    bit=(~m)&(m+1)
    for new,k,a,b in blocks:
        if new&bit and m|new!=m and cost[m]+k==cost[m|new] and cost[m]+k<=best+1:walk(m|new,pl+[(a,b)])
 walk(0,[])
 for x in range(256):
    w=[bool(x>>i&1) for i in range(8)]
    for op,a,b in res:w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
    assert w[-1]==target(x)
 return dict(gates=res,unshared_product_gates=best)
if __name__=='__main__':
 r=witnesses();(p/'upper.json').write_text(json.dumps(r));print(r)
