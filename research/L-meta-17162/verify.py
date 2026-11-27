"""Verify the census, circuit witnesses and signed rectangle bounds with Python integers."""
from collections import Counter
from itertools import combinations, permutations
from functools import lru_cache
from pathlib import Path
import json
D=Path(__file__).resolve().parent
def subsets(s):
    for k in range(len(s)+1):
        yield from combinations(s,k)
def rename(mask,p):return sum(1<<p[i] for i in range(len(p)) if mask&(1<<i))
def graphs():
    masks=[sum(1<<i for i in v) for v in subsets(range(4)) if len(v)>=2]
    classes=Counter()
    for family in subsets(masks):
        if any(sum(v>>i&1 for v in family)<2 for i in range(4)):continue
        if any((a&b).bit_count()>=2 for a,b in combinations(family,2)):continue
        classes[min(tuple(sorted(rename(v,perm) for v in family)) for perm in permutations(range(4)))]+=1
    assert sum(classes.values())==14 and len(classes)==4
    return classes
def check(family,mult):
    n=4+len(family)
    edges=[(i,4+j) for i in range(4) for j,v in enumerate(family) if v>>i&1]
    edge_count=len(edges); optimum=edge_count+3
    def target(mask):return any((mask>>i)&(mask>>j)&1 for i,j in edges)
    P=sorted(1<<a|1<<b for a,b in edges)
    N=[x for x in range(1<<n) if not target(x) and all(target(x|1<<i) for i in range(n) if not x>>i&1)]
    ms=[t for t in permutations(range(len(family)),4) if all(family[j]>>i&1 for i,j in enumerate(t))]
    assert ms
    gates=[]
    def add(op,a,b):
        assert 0<=a<n+len(gates) and 0<=b<n+len(gates) and a!=b
        gates.append((op,a,b));return n+len(gates)-1
    roots=[]
    for i in range(4):
        neighbors=[b for a,b in edges if a==i];v=neighbors[0]
        for b in neighbors[1:]:v=add('or',v,b)
        roots.append(add('and',i,v))
    out=roots[0]
    for root in roots[1:]:out=add('or',out,root)
    assert len(gates)==optimum
    for x in range(1<<n):
        wires=[x>>i&1 for i in range(n)]
        for op,a,b in gates:wires.append(wires[a]&wires[b] if op=='and' else wires[a]|wires[b])
        assert wires[out]==target(x)
    G=[]
    for perm in permutations(range(4)):
        cols=[rename(v,perm) for v in family]
        if set(cols)==set(family):G.append((*perm,*(4+family.index(v) for v in cols)))
    def signal(rows,i):return sum((x>>i&1)<<k for k,x in enumerate(rows))
    raw=tuple((signal(P,i),signal(N,i)) for i in range(n))
    def vals(g,signals):
        op,i,j=g
        return tuple(a&b if op=='and' else a|b for a,b in zip(signals[i],signals[j]))
    def choices(k):return [(op,a,b) for a,b in combinations(range(k),2) for op in ('and','or')]
    def trans(g,p):
        op,a,b=g;return (op,*sorted((p[a],p[b] if b<n else n)))
    programs=[(c,d) for c in choices(n) for d in choices(n+1)]
    labels={}
    for c,d in programs:
        if (c,d) in labels:continue
        orbit={(trans(c,g),trans(d,g)) for g in G}
        for pair in orbit:labels[pair]=(c,d)
    pairs=set(labels.values())
    single=set(choices(n))
    def traces(pair):
        a=vals(pair[0],raw);return a,vals(pair[1],(*raw,a))
    # Build sets of ordered pairs of boundary truth signatures. Canonicalize
    # only identical signatures; orbit transport is handled on certificates.
    pending={traces(pair) for pair in pairs}
    one={vals(c,raw) for c in single}
    tag='-'.join(map(str,family))
    certs=json.loads((D/('duals-'+tag+'.json')).read_text())+json.loads((D/('extra-'+tag+'.json')).read_text())
    zero=False;seen=set()
    @lru_cache(None)
    def eligible(sig):
        a,b=sig
        return [i for i in range(len(P)) if a>>i&1],[j for j in range(len(N)) if not b>>j&1]
    def rectmax(matrix,sig):
        rs,cs=eligible(sig); maxweight=0
        if not cs:return 0
        totals=[0]*len(cs);prev=0
        for index in range(1,1<<len(rs)):
            gray=index^(index>>1);bit=(gray^prev).bit_length()-1
            row=matrix[rs[bit]];sgn=1 if gray&(1<<bit) else -1
            for j,c in enumerate(cs):totals[j]+=sgn*row[c]
            maxweight=max(maxweight,sum(v for v in totals if v>0));prev=gray
        return maxweight
    for cert in certs:
        m=cert['weights']
        assert len(m)==len(P) and all(len(row)==len(N) and all(type(v)==int for v in row) for row in m)
        weight=sum(map(sum,m));assert weight==cert['total']
        rawcap=max(rectmax(m,s) for s in raw);assert rawcap>0
        zero|=weight>optimum*rawcap
        for g in G:
            a=[P.index(rename(x,g)) for x in P];b=[N.index(rename(x,g)) for x in N]
            M=tuple(tuple(m[i][j] for j in b) for i in a)
            if M in seen:continue
            seen.add(M)
            @lru_cache(None)
            def cap(sig):return max(rawcap,rectmax(M,sig))
            one.difference_update([s for s in one if weight>(optimum-1)*cap(s)])
            pending.difference_update([p for p in pending if weight>(optimum-2)*max(cap(p[0]),cap(p[1]))])
            if not one and not pending:break
        if zero and not one and not pending:break
    assert zero and not one and not pending,(family,len(one),len(pending))
    print(f'{family} orbit {mult}, gates {optimum}, inputs {1<<n}, matching {ms[0]}, {len(single)} single gates, {len(programs)} ordered pairs, {len(pairs)} pair orbits',flush=True)
if __name__=='__main__':
    for family,mult in graphs().items():check(family,mult)
