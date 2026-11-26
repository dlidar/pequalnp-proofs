"""Enumerate legal one-gate substitutions and score them on every six-vertex graph."""
from pathlib import Path
from itertools import combinations_with_replacement
from collections import Counter
import json
here=Path(__file__).resolve().parent
from design import M,ev
N=1<<15
full=(1<<N)-1
def pack(bits):
    return int.from_bytes(bytes(sum(bool(bits(8*i+j))<<j for j in range(8)) for i in range(N//8)), 'little')
raw=[pack(lambda x: x&(1<<j)) for j in range(15)]
truth=pack(lambda x:any(x&m==0 for m in M))
def evaluate(op,a,b,ws):
    if op=='not':return full^ws[a]
    if op=='and':return ws[a]&ws[b]
    return ws[a]|ws[b]
def visit(gs,out):
    original=raw.copy()
    for op,a,b in gs: original.append(evaluate(op,a,b,original))
    base=(truth^original[out]).bit_count()
    best=base; winners=[];dist=Counter()
    for i,(old,a,b) in enumerate(gs):
        j=15+i
        affected={j};suffix=[]
        for k,(op,c,d) in enumerate(gs[i+1:],j+1):
            if c in affected or d in affected:
                suffix.append((k,op,c,d));affected.add(k)
        choices=((op,c,d) for c,d in combinations_with_replacement(range(j),2) for op in ('and','or'))
        from itertools import chain
        # Empty AND and OR add constants. Unary monotone gates are equivalent to equal operands.
        # Empty NOT is another realization of true. Extra operands of NOT are ignored.
        ws=original.copy()
        for op,c,d in chain(choices,(('not',c,None) for c in range(j)),[('zero',0,None),('one',0,None)]):
            if (op,c,d)==(old,a,b) or (op,c,d)==(old,b,a):continue
            value=0 if op=='zero' else full if op=='one' else evaluate(op,c,d,original)
            if value==original[j]:score=base
            else:
                ws[j]=value
                for k,kind,p,q in suffix: ws[k]=evaluate(kind,p,q,ws)
                score=(ws[out]^truth).bit_count()
            dist[score]+=1
            if score<best:best=score;winners=[]
            if score==best:winners.append((i,op,c,d))
    return base,best,winners,dist
if __name__=='__main__':
    near=json.loads((here/'near.json').read_text())
    base,best,winners,dist=visit(near['gates'],near['out'])
    print('original',base,'alternatives',dist.total(),'minimum',best,'at minimum',dist[best],'first',winners[:4],flush=True)
    assert (base,best,dist.total(),dist[best])==(708,708,62125,6)
