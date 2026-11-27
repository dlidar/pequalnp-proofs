from functools import lru_cache
from pathlib import Path
import json

p=Path(__file__).resolve().parent
@lru_cache(None)
def within(s,budget):
    if len(s)>budget:return None
    if not s:return ()
    t=max(s,key=int.bit_count);remain=set(s)-{t}
    if t.bit_count()-1>budget:return None
    subs=[a for a in range(1,t) if a&t==a]
    for j,a in enumerate(subs):
        for b in subs[j+1:]:
            if a|b!=t:continue
            new=remain|{v for v in (a,b) if v.bit_count()>1}
            prev=within(frozenset(new),budget-1)
            if prev is not None:return prev+((a,b),)
    return None
if __name__=="__main__":
    import sys
    partial=len(sys.argv)>1
    rows=[list(tuple(map(int,x.split(','))) for x in l.split()) for l in (p/('partial-covers.txt' if partial else 'covers.txt')).read_text().splitlines()]
    best=14;winner=None;valid=0
    for pairs in rows:
        s=frozenset(v for ab in pairs for v in ab if v.bit_count()>1)
        for k in range(len(s),14-(2*len(pairs)-1)):
            g=within(s,k)
            if g is not None:
                valid+=1
                if len(g)+2*len(pairs)-1<best:
                    best=len(g)+2*len(pairs)-1;winner=dict(pairs=pairs,unions=g)
                break
    print('minimum',best,'of',len(rows),'survivors',valid,'at most 13',flush=True)
    (p/('partial-budget.json' if partial else 'budget.json')).write_text(json.dumps({'minimum':best,'survivors':len(rows),'at_most_13':valid,'witness':winner}))
