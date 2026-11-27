"""Check the budget below an explicit shared 13-gate repair on all admissible covers."""
from pathlib import Path
import json
from budget import within,p
best=13;winning=None
for line in (p/'partial-covers.txt').open():
    pairs=[tuple(map(int,t.split(','))) for t in line.split()]
    s=frozenset(t for ab in pairs for t in ab if t.bit_count()>1)
    budget=best-2*len(pairs)
    if len(s)>budget:continue
    plan=within(s,budget)
    if plan is not None:
        best=2*len(pairs)-1+len(plan);winning=dict(pairs=pairs,unions=plan)
        print(best,winning,flush=True)
        for k in range(len(s),len(plan)):
            g=within(s,k)
            if g is not None:
                best=2*len(pairs)-1+len(g);winning=dict(pairs=pairs,unions=g);break
assert winning is not None and best == 12
available={1 << i for i in range(8)}
for a,b in winning['unions']:
    assert a in available and b in available
    available.add(a | b)
assert all(a in available and b in available for a,b in winning['pairs'])
assert len(winning['unions'])+2*len(winning['pairs'])-1==best
def serves(mask):
    return any(mask & a and mask & b for a,b in winning['pairs'])
bounds=json.loads((p/'bounds.json').read_text())
assert all(serves(m) for m in bounds['positive'])
assert not any(serves(m) for m in (7,21,56,112,144))
print('final',best,flush=True)
(p/'partial-min.json').write_text(json.dumps(dict(minimum=best,witness=winning)))
