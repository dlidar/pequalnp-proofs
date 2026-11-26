"""Enumerate unresolved labelled 4+4 incidence instances modulo separate permutations and transpose."""
from itertools import permutations,combinations
from pathlib import Path
import json
def classes():
    n=4;perms=list(permutations(range(n)));covered=set();reps=[]
    for g in range(1<<16):
        if g in covered:continue
        pairs=[(i,j) for i in range(n) for j in range(n) if (g>>(4*i+j))&1]
        if len(pairs)<7:continue
        rows=[(g>>(4*i))&15 for i in range(4)]
        if any((a & b).bit_count()>1 for i,a in enumerate(rows) for b in rows[:i]):continue
        adj=[set() for _ in range(8)]
        for i,j in pairs:adj[i].add(4+j);adj[4+j].add(i)
        rem={i for i,r in enumerate(adj) if r};components=[]
        while rem:
            part=set();stack=[rem.pop()]
            while stack:
                i=stack.pop();part.add(i);new=adj[i]&rem;rem-=new;stack.extend(new)
            components.append(part)
        if all(sum(len(adj[i]) for i in c)<2*len(c) for c in components):continue
        if len(components)==1 and all(len(adj[i])==2 for i in components[0]):continue
        orbit=set()
        for a in perms:
            for b in perms:
                orbit.add(sum(1<<(4*a[i]+b[j]) for i,j in pairs))
                orbit.add(sum(1<<(4*b[j]+a[i]) for i,j in pairs))
        covered.update(orbit)
        k=min(t.bit_count() for t in range(256) if all(t & ((1<<i)|(1<<(4+j))) for i,j in pairs))
        reps.append(dict(mask=g,edges=pairs,cover=k,star_gates=len(pairs)+k-1,orbit=len(orbit)))
    assert sum(r['orbit'] for r in reps)==2208
    return reps
if __name__=='__main__':
 r=classes();print([(x['mask'],x['star_gates'],x['orbit']) for x in r])
