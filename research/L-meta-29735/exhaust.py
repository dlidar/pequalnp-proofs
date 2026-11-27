"""Exact attainable coverage by total rank, for small field towers."""
import itertools
import json
from collections import Counter
from functools import reduce
from operator import xor

def census(h, m, polynomial):
    q = 2**h
    size = q**m
    def mul(a,b):
        product = 0
        while b:
            if b & 1:
                product ^= a
            b >>= 1
            a <<= 1
            if a >= size:
                a ^= polynomial
        return product
    table = [[mul(a,b) for b in range(size)] for a in range(size)]
    assert all(len(set(row)) == size for row in table[1:])
    def power(a,n):
        result = 1
        for _ in range(n):
            result = table[a][result]
        return result
    scalars = [a for a in range(size) if power(a,q)==a]
    assert len(scalars)==q
    coords = {0:()}
    while len(coords)<size:
        v = next(x for x in range(size) if x not in coords)
        coords = {x ^ table[a][v]:prev+(a,) for x,prev in coords.items() for a in scalars}
    assert len(coords[1])==m
    records=Counter()
    masks={}
    for columns in itertools.product(range(size),repeat=m):
        values=[reduce(xor,(table[x][y] for x,y in zip(coords[w],columns)),0) for w in range(size)]
        rank=next(r for r in range(m+1) if q**r==len(set(values)))
        assert values.count(0)*q**rank==size
        mask=0
        for z in range(1,size):
            residual=[table[z][x]^v for x,v in enumerate(values)]
            hit=len(set(residual))<size
            assert hit==any(table[z][x]==values[x] for x in range(1,size))
            if hit: mask |= 1<<(z-1)
        records[rank,mask.bit_count()]+=1
        masks[mask]=min(rank,masks.get(mask,m+1))
    target=m*(q-1)
    front=[{0}]+[set() for _ in range(target)]
    for cost in range(1,target+1):
        for mask,rank in masks.items():
            if 0<rank<=cost:
                front[cost].update(prev|mask for prev in front[cost-rank])
        front[cost].update(front[cost-1])
    attained=[max(s.bit_count() for s in layer) for layer in front]
    predicted=[]
    for cost in range(target+1):
        a,b=divmod(cost,q-1)
        left=q**(m-a)-b*q**max(0,m-a-1)
        predicted.append(size-left)
    assert attained==predicted
    return dict(q=q,m=m,linear_maps=size**m,maximum_by_budget=attained,
                single_map_spectrum=[(r,s,n) for (r,s),n in sorted(records.items())])
if __name__=='__main__':
    print(json.dumps([census(h,m,p) for h,m,p in [(1,3,11),(2,2,19),(3,1,11)]],indent=2))
