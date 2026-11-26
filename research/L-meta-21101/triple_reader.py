"""Test one internal wire with three outgoing uses and every other non-output wire read once."""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import json
from shared_profiles import raw,mask,cover,total
@lru_cache(maxsize=65536)
def walk(ws,remaining):
    # Tags identify ordinary raw inputs, internal wires, and the selected triple reader.
    if len(ws)+remaining==1:return ws[0][0]==mask
    seen=0
    for sig,_ in ws:seen |= cover(sig)
    if seen!=total:return False
    for i,j in combinations(range(len(ws)),2):
        a,b=ws[i],ws[j];rest=ws[:i]+ws[i+1:j]+ws[j+1:]
        for v in [a[0]&b[0],a[0]|b[0]]:
            ordinary=(*rest,(v,1))
            if walk(tuple(sorted(ordinary)),remaining):return True
            for sig,tag in [a,b]:
                if (remaining,tag) in [(2,1),(1,2)]:
                    if walk(tuple(sorted((*ordinary,(sig,2)))),remaining-1):return True
    return False
if __name__=='__main__':
    witness=walk(tuple(sorted((x,0) for x in raw)),2)
    print('One internal triple reader possible:',witness,flush=True)
    Path(__file__).with_name('triple_reader.json').write_text(json.dumps({'one_internal_triple_reader':witness})+'\n')
