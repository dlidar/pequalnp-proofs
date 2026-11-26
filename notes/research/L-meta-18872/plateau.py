"""Explore all moves preserving the best full-table error, with a configurable state limit."""
from collections import deque
from neighbors import visit,here,json
import sys
limit=int(sys.argv[1]) if len(sys.argv)>1 else 80
near=json.loads((here/'near.json').read_text())
def ordered(g):
    op,a,b=g
    return (op,a,b) if b is None or a<=b else (op,b,a)
start=tuple(map(ordered,near['gates']))
q=deque([start]);seen={start};expanded=0;minscore=708;total=0
while q and expanded<limit:
    parent=q.popleft()
    _,score,edits,dist=visit(parent,near['out'])
    total+=dist.total();expanded+=1
    if score<minscore:
        print('improvement',score,edits[0],flush=True)
        minscore=score
        break
    for i,op,a,b in edits:
        assert op in ('and','or','not')
        candidate=parent[:i]+(ordered((op,a,b)),)+parent[i+1:]
        if candidate not in seen:
            seen.add(candidate);q.append(candidate)
print('expanded',expanded,'seen',len(seen),'remaining',len(q),'checks',total,'minimum',minscore,flush=True)
