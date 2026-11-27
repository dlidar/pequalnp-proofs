"""Validate the gate list independently by bit-parallel evaluation and direct spin enumeration."""
from itertools import product,permutations
from collections import defaultdict
from random import Random
from circuit import compile_circuit
from functools import lru_cache
import sys
rng=Random(393)
@lru_cache(maxsize=32)
def reference(perm):
    n=len(perm); m=2*n; result={}
    labels=[(sum((x>>i^x>>(n+i))&1 for i in range(n)),sum((x>>i^x>>(n+perm[i]))&1 for i in range(n))) for x in range(2**m)]
    for p in product(range(3),repeat=m):
        hist=[0]*(n+1)**2
        for x,(r,b) in enumerate(labels):
            if all(not d or d==1+((x>>i)&1) for i,d in enumerate(p)):hist[r*(n+1)+b]+=1
        result[p]=tuple(hist)
    return result
def bits(v,k):return [(v>>j)&1 for j in range(k)]
def check(n,limit):
    g,(num,ordw,valid,selected)=compile_circuit(n)
    m=2*n; expected=[]; ins=[]
    def add(perm,allow,H,p,z,junk,fiber):
        b=[0,1]+[int(perm[i]==j) for i in range(n) for j in range(n)]
        b += [(v>>d)&1 for d in range(3) for v in allow]
        b += [s for cell in H for s in bits(cell,2*n+1)]
        b += [int(d!=0) for d in p]+[int(d==2) if d else junk[i] for i,d in enumerate(p)]+bits(z,4*n)
        assert len(b)==g.inputs
        expected.append((len(fiber),p in fiber,fiber.index(p) if p in fiber else None,fiber[z] if z<len(fiber) else None))
        ins.append(b)
    for perm in permutations(range(n)):
        ref=reference(perm); pins=list(ref)
        masks=product(range(8),repeat=m) if n==1 else [tuple([7]*m),tuple([0]*m)]+[tuple(rng.randrange(8) for _ in range(m)) for _ in range(limit)]
        for allow in masks:
            fs=defaultdict(list)
            for p,h in ref.items():
                if all(v&(1<<d) for v,d in zip(allow,p)):fs[h].append(p)
            for f in fs.values():f.sort(key=lambda p:sum(d*3**i for i,d in enumerate(p)))
            all_h=list(set(ref.values())) if n==1 else rng.sample(list(fs),min(3,len(fs)))
            for H in [*all_h,tuple([2**(2*n+1)-1]*(n+1)**2)]:
                f=fs[H]
                ps=rng.sample(pins,min(2,len(pins)))+[rng.choice(f)] if f else [rng.choice(pins)]
                for p in ps:
                    for z in {0,max(0,len(f)-1),len(f)}:
                        add(perm,allow,H,p,z,bits(rng.randrange(2**m),m),f)
    for j,(op,a,b) in enumerate(g.program):
        assert 0<=a<g.inputs+j and (b is None if op=='not' else 0<=b<g.inputs+j and op in ('and','or'))
    for start in range(0,len(ins),256):
        samples=ins[start:start+256]; mask=(1<<len(samples))-1
        wires=[sum(b<<i for i,b in enumerate(col)) for col in zip(*samples)]
        for op,a,b in g.program:
            wires.append((wires[a]^mask) if op=='not' else (wires[a]&wires[b] if op=='and' else wires[a]|wires[b]))
        for i,(count,yes,rank,pick) in enumerate(expected[start:start+256]):
            bit=lambda k: (wires[k]>>i)&1
            val=lambda xs:sum(bit(k)<<j for j,k in enumerate(xs))
            assert val(num)==count and bit(valid)==yes
            if yes:assert val(ordw)==rank
            if pick is not None:assert tuple(1+bit(b) if bit(a) else 0 for a,b in selected)==pick
    print('n',n,'inputs',g.inputs,'gates',len(g.program),'validated vectors',len(ins),flush=True)
for n in map(int,sys.argv[1:]):check(n,15)
