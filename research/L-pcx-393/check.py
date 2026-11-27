from collections import Counter, defaultdict
from itertools import permutations,product
from random import Random
from inventory import distributions,index
rng = Random(393)
instances = pins = queries = 0
for n in range(1,4):
    for perm in permutations(range(n)):
        cells = []
        for x in range(4**n):
            bit = lambda k: (x>>k)&1
            r = sum(bit(i)!=bit(n+i) for i in range(n))
            b = sum(bit(i)!=bit(n+perm[i]) for i in range(n))
            cells.append(r*(n+1)+b)
        expected = {}
        for p in product(range(3), repeat=2*n):
            counts = [0]*(n+1)**2
            for x,cell in enumerate(cells):
                if all(v==0 or v==1+((x>>i)&1) for i,v in enumerate(p)):
                    counts[cell]+=1
            expected[p] = tuple(counts)
            pins+=1
        masks = list(product(range(8),repeat=2*n)) if n==1 else [
            (7,)*(2*n), (0,)*(2*n), (1,)*(2*n),
            *[tuple(rng.randrange(8) for _ in range(2*n)) for _ in range(45)]]
        for allow in masks:
            fibers=defaultdict(list)
            for p,h in expected.items():
                if all(a & 1<<v for a,v in zip(allow,p)): fibers[h].append(p)
            assert distributions(perm,allow)==Counter({h:len(f) for h,f in fibers.items()})
            instances+=1
            for h in rng.sample(list(fibers),min(len(fibers),4)):
                f=sorted(fibers[h],key=lambda p:sum(v*3**i for i,v in enumerate(p)))
                for z in {0,len(f)//2,len(f)-1,len(f)}:
                    p=rng.choice(f)
                    assert index(perm,allow,h,p,z)==(len(f),True,f.index(p),f[z] if z<len(f) else None)
                    queries+=1
print('exact comparisons:',instances,'permission/layout pairs,',pins,'pin histograms,',queries,'rank/select queries')
