"""Which pairs of extra leaf labels permit a binary formula on the 4 by 5 promise?"""
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
import json
from pathlib import Path

rows,cols,mask=4,5,245567
cells=list(range(rows*cols))
positive=[x for x in cells if mask>>x&1]
negative=[x for x in cells if not mask>>x&1]
pairs=[(p,n) for p in positive for n in negative]
def raw(j):
    return sum(1<<x for x in cells if j in (x//cols,rows+x%cols))
inputs=tuple(map(raw,range(rows+cols)))
@lru_cache(maxsize=131072)
def distinguishes(w):
    return sum(1<<i for i,(p,n) in enumerate(pairs) if (w>>p)&1 and not (w>>n)&1)
full=(1<<len(pairs))-1
def separates(ws):
    v=0
    for x in ws:v |= distinguishes(x)
    return v==full
@lru_cache(maxsize=65536)
def tree(ws):
    if len(ws)==1:return () if ws[0]==mask else None
    if not separates(ws):return None
    seen=set()
    for i,j in combinations(range(len(ws)),2):
        a,b=ws[i],ws[j]
        if (a,b) in seen:continue
        seen.add((a,b))
        rest=ws[:i]+ws[i+1:j]+ws[j+1:]
        for op,c in [('and',a&b),('or',a|b)]:
            child=tree(tuple(sorted((*rest,c))))
            if child is not None:return ((op,a,b),)+child
    return None
def verify(extra,path):
    ws=[*inputs,*(inputs[i] for i in extra)]
    for op,a,b in path:
        ws.remove(a);ws.remove(b);ws.append((a&b) if op=='and' else (a|b))
    assert ws==[mask] and len(path)==10
assert all(not separates(inputs[:i]+inputs[i+1:]) for i in range(len(inputs)))
out=[]
for extra in combinations_with_replacement(range(len(inputs)),2):
    r=tree(tuple(sorted((*inputs,*(inputs[x] for x in extra)))))
    if r is not None:
        verify(extra,r);out.append({'repeated':extra,'merges':r})
print(len(out),[z['repeated'] for z in out],flush=True)
Path(__file__).with_name('formula_profiles.json').write_text(json.dumps(out,indent=1)+'\n')
