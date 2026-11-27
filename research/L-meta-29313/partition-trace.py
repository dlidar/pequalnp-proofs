from partitions import boxes, cells, r, c, cap, score, p
from functools import lru_cache
import json
trace=[]
@lru_cache(None)
def exclude(rem,k,slack):
    if not rem:
        assert k>0
        trace.append([hex(rem),k,slack,-1])
        return
    if k==0:
        trace.append([hex(rem),k,slack,-1])
        return
    best=None
    for i in range(r*c):
        if not rem>>i&1:continue
        options=[(box,d) for box,d in cells[i] if d<=slack and box&rem==box]
        if best is None or len(options)<len(best):
            pivot,best=i,options
        if not best:break
    for box,d in best:exclude(rem^box,k-1,slack-d)
    trace.append([hex(rem),k,slack,pivot])
exclude((1<<(r*c))-1,14,14*cap-score)
(p/'partition-trace.json').write_text(json.dumps(trace,separators=(',',':')))
print(len(trace),'proof nodes')
