"""Evaluate every promised input and exhaust circuits with at most three gates."""
from itertools import combinations
cells=[(u,v) for u in range(5) for v in range(5)]
top=(1<<len(cells))-1
raw=tuple(sum(1<<i for i,(u,v) in enumerate(cells) if j in (u,5+v)) for j in range(10))
target=sum(1<<i for i,(u,v) in enumerate(cells) if [0,0,0,1,30][u]>>v&1)
assert ((raw[3]&raw[5])|(raw[4]&(top^raw[5])))==target
# Free constants cover empty input lists and out-of-range/default wires.
# Unary AND/OR, repeated operands and empty NOT introduce no other signals.
states={frozenset((*raw,0,top))}
for depth in range(1,4):
    next_states=set()
    for wires in states:
        candidates={top^a for a in wires}
        for a,b in combinations(wires,2):
            candidates.update([a&b,a|b])
        assert target not in wires|candidates
        if depth<3:
            next_states.update(wires|{x} for x in candidates-wires)
    print('checked depth',depth,'from',len(states),'sets')
    states=next_states
print('Exact minimum four across 25 promised inputs.')
