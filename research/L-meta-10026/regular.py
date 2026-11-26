"""Find short integral multiples of a symmetric fractional cover."""
from extremal import rows,maximal,rectangle,w
from collections import deque,Counter
from itertools import product
import json
# Multiplication in F_5[s]/(s^2-2).
def order(x,y):
    a,b=1,0
    for n in range(1,25):
        a,b=(a*x+2*b*y)%5,(a*y+b*x)%5
        if (a,b)==(1,0):return n
u,v=next((x,y) for x,y in product(range(5),repeat=2) if order(x,y)==24)
fs=[lambda x,y:(x+1,y),lambda x,y:(u*x+2*v*y,v*x+u*y)]
gp=[[a%5+5*(b%5) for a,b in (f(i%5,i//5) for i in range(25))] for f in fs]
by=dict(maximal())
d=set(by);orbits=[]
while d:
    q=deque([min(d)]);d.remove(q[0]);o=[]
    while q:
        p=q.popleft();o.append([p,by[p]])
        for f in gp:
            t=sum(1<<f[i] for i in range(25) if p>>i&1)
            if t in d:d.remove(t);q.append(t)
    orbits.append(o)
o=min(orbits,key=len);h=Counter(c for a,b in o for c in rectangle(a,b))
print('orbit sizes',list(map(len,orbits)),'shortest coverage',set(h.values()),'zeros',len(h))
assert len(h)==600 and len(set(h.values()))==1
(w/'fraction.json').write_text(json.dumps(o))
