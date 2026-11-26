"""Enumerate excess reads in ten binary gates with all nine raws used and every gate live."""
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path
d=Path(__file__).resolve().parent
mask=245567
rows=range(20)
raw=[sum(1<<r for r in rows if i in (r//5,4+r%5)) for i in range(9)]
pairs=[(a,b) for a in rows if mask>>a&1 for b in rows if not mask>>b&1]
total=(1<<len(pairs))-1
@lru_cache(maxsize=32768)
def cover(value):
    return sum(1<<i for i,(a,b) in enumerate(pairs) if value>>a&1 and not value>>b&1)
initial=tuple(sorted((v<<4)|j for j,v in enumerate(raw)))
def moves(s,e):
    for i,j in combinations(range(len(s)),2):
        a,b=s[i],s[j]
        rest=s[:i]+s[i+1:j]+s[j+1:]
        seen=0
        for r in rest:seen |= cover(r>>4)
        a0,b0=a>>4,b>>4
        for op,v in [('and',a0&b0),('or',a0|b0)]:
            m=seen|cover(v)
            for keep in [(),(a,),(b,),(a,b)]:
                if len(keep)>e:continue
                cut=m
                for x in keep:cut |= cover(x>>4)
                if cut==total:
                    yield (op,a,b,keep),tuple(sorted((*rest,*keep,(v<<4)|9)))
@lru_cache(maxsize=65536)
def possible(s,e):
    if len(s)+e==1:return frozenset([()]) if s[0]>>4==mask else frozenset()
    out=set()
    for (_,a,b,keep),child in moves(s,e):
        tags=tuple(x&15 for x in keep)
        for suffix in possible(child,e-len(tags)):
            out.add(tuple(sorted(tags+suffix)))
    return frozenset(out)
def reconstruct(s,prof):
    if len(s)+len(prof)==1:return []
    for move,child in moves(s,len(prof)):
        need=list(prof)
        for x in move[3]:
            if (x&15) not in need:break
            need.remove(x&15)
        else:
            if tuple(need) in possible(child,len(need)):
                return [move]+reconstruct(child,tuple(need))
    raise AssertionError
def decode(prof,moves_used):
    available=[((v<<4)|i,i) for i,v in enumerate(raw)]
    gates=[]
    for op,a,b,keep in moves_used:
        ia=next(i for i,q in enumerate(available) if q[0]==a)
        ib=next(i for i,q in enumerate(available) if q[0]==b and i!=ia)
        xa,xb=available[ia],available[ib]
        gates.append((op,xa[1],xb[1]))
        available=[q for i,q in enumerate(available) if i not in (ia,ib)]
        extra=list(keep)
        for q in (xa,xb):
            if q[0] in extra:available.append(q);extra.remove(q[0])
        v=(a>>4)&(b>>4) if op=='and' else (a>>4)|(b>>4)
        available.append(((v<<4)|9,8+len(gates)))
    assert len(gates)==10 and available==[((mask<<4)|9,18)]
    reads=[0]*18
    for _,a,b in gates:reads[a]+=1;reads[b]+=1
    assert min(reads)>0
    assert sorted((i if i<9 else 9) for i in range(18) for _ in range(reads[i]-1))==list(prof)
    for r in rows:
        vals=[bool(v>>r&1) for v in raw]
        for op,a,b in gates:vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
        assert vals[-1]==bool(mask>>r&1)
    return {'excess_labels':prof,'gates':gates}
if __name__=='__main__':
    profiles=sorted(possible(initial,2))
    print('Raw labels 0..8; internal label 9.',profiles,flush=True)
    cert=[decode(p,reconstruct(initial,p)) for p in profiles]
    (d/'shared_profiles.json').write_text(json.dumps(cert,indent=1)+'\n')
