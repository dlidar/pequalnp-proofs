"""Enumerate legal tests and evaluate all 156 merged-star circuits."""
from itertools import combinations
from functools import reduce
from operator import or_
from random import Random
from math import exp

N = 13
ALL = (1 << N) - 1
rows = [sum(1 << ((p-d) % N) for d in (0,1,3,9)) for p in range(N)]
cols = [
    sum(1 << p for p,r in enumerate(rows) if r >> l & 1) for l in range(N)]
edges = [(p,l) for p in range(N) for l in range(N) if rows[p] >> l & 1]
pairs = list(combinations(range(N), 2))
def caps(neighbors):
    return [s for s in range(1<<N) if all((s & n).bit_count() <= 2 for n in neighbors)]
def maximal_tests():
    masks = []
    pcap, lcap = caps(cols), caps(rows)
    for p in pcap:
        blocked = reduce(or_, (rows[i] for i in range(N) if p >> i & 1), 0)
        for l in lcap:
            if not l & blocked: masks.append((p,l))
    pool = set(masks)
    maximal = [(p,l) for p,l in masks if not any(
        (not (p>>i&1) and (p|1<<i,l) in pool) or
        (not (l>>i&1) and (p,l|1<<i) in pool) for i in range(N))]
    return maximal
def losses(p,l):
    data = [(p,l,rows),(l,p,cols)]
    return sum(1 << (side*78+k) for side,(a,b,neighbors) in enumerate(data)
               for k,(i,j) in enumerate(pairs)
               if a & (1<<i|1<<j) and b & (neighbors[i]|neighbors[j]))
def merge_program(side, u, v):
    neighbors = (rows,cols)[side]
    program=[]
    def node(op,a,b):
        program.append((op,a,b));return 26+len(program)-1
    def disj(xs):
        it=iter(xs);r=next(it)
        for i in it:r=node('or',r,i)
        return r
    base,other=(0,13) if side==0 else (13,0)
    blocks=[]
    for i in range(N):
        if i==v:continue
        n=neighbors[i]|(neighbors[v] if i==u else 0)
        center=node('or',base+u,base+v) if i==u else base+i
        blocks.append(node('and',center,disj(other+j for j in range(N) if n>>j&1)))
    disj(blocks)
    assert len(program)==63
    return program
def verify(tests,covers):
    samples=[(1<<p,1<<l) for p,l in edges]+tests
    signatures=[sum(1<<i for i,(p,l) in enumerate(samples) if (p|l<<13)>>j&1) for j in range(26)]
    gold=(1<<len(edges))-1
    for side in range(2):
        for k,(i,j) in enumerate(pairs):
            w=signatures.copy()
            for op,a,b in merge_program(side,i,j):w.append(w[a]|w[b] if op=='or' else w[a]&w[b])
            actual=w[-1];assert actual & gold == gold
            errs=actual>>len(edges)
            expected=sum(1<<n for n,coverage in enumerate(covers) if coverage>>(side*78+k)&1)
            assert errs==expected
def search(covers,k,iterations):
    rng=Random(k)
    for trial in range(20):
        deck=rng.sample(range(len(covers)),k)
        for t in range(iterations):
            slot=rng.randrange(k)
            others=reduce(or_,(covers[x] for j,x in enumerate(deck) if j!=slot),0)
            old=(others|covers[deck[slot]]).bit_count()
            if old==156:return deck
            new=rng.randrange(len(covers));score=(others|covers[new]).bit_count()
            temp=1.2*(1-(t%800)/800)+0.05
            if score>=old or rng.random()<exp((score-old)/temp):deck[slot]=new
    return None
if __name__=='__main__':
    import json
    from pathlib import Path
    w=Path(__file__).resolve().parent
    tests=maximal_tests(); covers=[losses(*t) for t in tests]
    assert len(tests)==468 and max(p.bit_count()+l.bit_count() for p,l in tests)==7
    verify(tests,covers)
    print('52 positives and 468 maximal negatives checked independently on 156 actual 63-gate programs',flush=True)
    for k in [6,7,8]:
        result=search(covers,k,12000)
        if result:
            chosen=[tests[i] for i in result];print('hitting design',k,chosen,flush=True)
            (w/'design.json').write_text(json.dumps(chosen));break
