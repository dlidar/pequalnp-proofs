"""Check all single-gate repairs of the 36 specified edge-deletion circuits.

For a single edit, evaluating the suffix with the edited wire forced low/high
gives its exact Boolean response on every boundary row, even under reconvergence.
"""
from collections import deque, Counter
from functools import lru_cache
from mcgee import E, N, V, allv, best
import json

@lru_cache(None)
def count_ind(s):
    if not s:
        return 1
    i = (s & -s).bit_length() - 1
    t = s ^ (1 << i)
    return count_ind(t) + count_ind(t & ~N[i])

def girth():
    lengths = []
    for a,b in E:
        queue = deque([(a,0)])
        seen = {a}
        while queue:
            i,d = queue.popleft()
            if i == b:
                lengths.append(d+1)
                break
            for j in V:
                if j not in seen and N[i] >> j & 1 and {i,j} != {a,b}:
                    seen.add(j)
                    queue.append((j,d+1))
    return min(lengths)

def maximal(s,chosen,covered):
    if not s:
        if covered == allv:
            yield chosen
        return
    bit = s & -s
    i = bit.bit_length() - 1
    t = s ^ bit
    yield from maximal(t,chosen,covered)
    yield from maximal(t & ~N[i],chosen | bit,covered | bit | N[i])

def star_circuit(edges):
    cover = allv ^ best(allv)
    groups = {}
    for a,b in edges:
        if not (cover >> a & 1):
            a,b = b,a
        assert cover >> a & 1
        groups.setdefault(a,[]).append(b)
    gates = []
    def gate(op,i,j):
        gates.append((op,i,j))
        return 23 + len(gates)
    def join(wires):
        u,*rest = wires
        for v in rest:
            u = gate('or',u,v)
        return u
    join([gate('and',a,join(vs)) for a,vs in sorted(groups.items())])
    return gates

def apply(op,a,b,mask):
    if op == 'and':
        return a & b
    if op == 'or':
        return a | b
    return mask ^ a

def run(gates,inputs,mask,fix=None):
    vals = list(inputs)
    for k,(op,i,j) in enumerate(gates):
        vals.append(fix[1] if fix and fix[0] == k else apply(op,vals[i],vals[j],mask))
    return vals

def main():
    negatives = list(maximal(allv,0,0))
    assert len(set(negatives)) == len(negatives)
    for s in negatives:
        assert all(not(s>>i&1 and s>>j&1) for i,j in E)
        assert all(s>>i&1 or s&N[i] for i in V)
    rows = [(1<<a)|(1<<b) for a,b in E] + negatives
    mask = (1<<len(rows))-1
    target = (1<<len(E))-1
    inputs = [sum(1<<k for k,row in enumerate(rows) if row>>i&1) for i in V]
    full = star_circuit(E)
    assert len(full)==49 and run(full,inputs,mask)[-1]==target
    edits, hits, costs, distances = 0, [], Counter(), Counter()
    for idx,(a,b) in enumerate(E):
        gates = star_circuit(E[:idx]+E[idx+1:])
        vals = run(gates,inputs,mask)
        assert vals[-1] == target ^ (1<<idx)
        costs[len(gates)] += 1
        distances[count_ind(allv & ~((1<<a)|(1<<b)|N[a]|N[b]))] += 1
        for k,old in enumerate(gates):
            lo,hi = (run(gates,inputs,mask,(k,value))[-1] for value in (0,mask))
            if (target ^ lo) & (target ^ hi):
                continue
            delta = lo ^ hi
            needed = target ^ lo
            for j in range(24+k):
                for i in range(j+1):
                    for op in ('or','and'):
                        edits += 1
                        if apply(op,vals[i],vals[j],mask)&delta == needed:
                            hits.append(((a,b),k,op,i,j))
                edits += 1
                if (mask ^ vals[j]) & delta == needed:
                    hits.append(((a,b),k,'not',j))
    return dict(girth=girth(),edges=len(E),maximal_negatives=len(negatives),full=len(full),
                template_lengths=dict(sorted(costs.items())),false_negative_counts=dict(sorted(distances.items())),
                candidates_at_viable_slots=edits,boundary_survivors=hits)
if __name__=='__main__':
    print(json.dumps(main(),indent=2))
