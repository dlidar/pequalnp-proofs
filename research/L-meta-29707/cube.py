"""Worst minimum monotone formula interpolating oppositely incomparable labels."""
import json
from pathlib import Path
def examine(n):
    m=1<<n
    full=(1<<m)-1
    raw=[sum(((x>>i)&1)<<x for x in range(m)) for i in range(n)]
    cost={0:0,full:0,**dict.fromkeys(raw,1)}
    for k in range(2,32):
        new=set()
        for a in range(1,k//2+1):
            left=[u for u,w in cost.items() if w==a]
            right=[v for v,w in cost.items() if w==k-a]
            for u in left:
                for v in right:new.update((u&v,u|v))
        for u in new:cost.setdefault(u,k)
    assert len(cost)==[2,3,6,20,168][n]
    inc=[sum(1<<y for y in range(m) if x&y!=x and x&y!=y) for x in range(m)]
    masks=[full]*(1<<m);hist={};example={}
    for z in range(1<<m):
        if z:
            bit=z&-z;masks[z]=masks[z^bit]&inc[bit.bit_length()-1]
        o=masks[z]
        k=min(w for u,w in cost.items() if not z&u and o&u==o)
        hist[k]=hist.get(k,0)+1
        example.setdefault(k,{'Z':[i for i in range(m) if z>>i&1],'O':[i for i in range(m) if o>>i&1]})
    return {'coordinates':n,'monotone_functions':len(cost),'histogram':hist,'worst':max(hist),'example':example[max(hist)]}
if __name__=='__main__':
 p=Path(__file__).resolve().parent
 rows=[examine(k) for k in range(5)]
 for r in rows:print(r)
 (p/'cube.json').write_text(json.dumps(rows,indent=2)+'\n')
