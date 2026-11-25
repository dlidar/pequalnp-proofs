"""Test every one-gate replacement in every canonical one-edge-deletion star circuit."""
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json
from random import Random

def star(edges):
    gates = []
    def put(op, a, b):
        gates.append((op, a, b))
        return 39 + len(gates)
    def disjoin(xs):
        v = xs[0]
        for x in xs[1:]:
            v = put('or', v, x)
        return v
    roots = [put('and', i, disjoin([b for a,b in edges if a == i])) for i in sorted({a for a,b in edges})]
    out = disjoin(roots)
    return gates, out

def test_masks(edges):
    masks = {0, (1 << 40)-1}
    masks.update(1 << i for i in range(40))
    masks.update((1 << i) | (1 << j) for i,j in combinations(range(40),2))
    rng = Random(9838)
    for _ in range(200):
        order = list(range(40))
        rng.shuffle(order)
        s = 0
        for i in order:
            x = s | (1 << i)
            if not any((x >> a) & (x >> b) & 1 for a,b in edges):
                s = x
        masks.add(s)
    return sorted(masks)

def survivors(gates, out, raw, t, full):
    def run(wires, tail):
        for op,a,b in tail:
            wires.append(wires[a] & wires[b] if op=='and' else wires[a] | wires[b])
        return wires
    wires = run(list(raw), gates)
    assert len(gates) == 113 and wires[out] != t
    for j in range(len(gates)):
        before = wires[:40+j]
        low, high = [run(before+[bit], gates[j+1:])[out] for bit in [0,full]]
        if low & ~t or t & ~high:
            continue
        pos, neg = t & ~low, high & ~t
        # Constants include all missing and out-of-range wire values.
        inputs = before+[0,full]
        def fits(v):
            return not (pos & ~v or neg & v)
        for a,v in enumerate(inputs):
            if fits(full^v):
                yield (j,'not',a)
        for op in ['and','or']:
            possible = [(a,v) for a,v in enumerate(inputs) if not (pos & ~v if op=='and' else neg & v)]
            for (a,v),(b,w) in combinations_with_replacement(possible,2):
                if fits(v & w if op=='and' else v | w):
                    yield (j,op,a,b)

def main():
    edges = [tuple(e) for e in json.loads(Path(__file__).with_name('edges.json').read_text())]
    tests = test_masks(edges)
    full = (1 << len(tests))-1
    raw = [sum(((x>>a)&1)<<j for j,x in enumerate(tests)) for a in range(40)]
    target = 0
    for a,b in edges:
        target |= raw[a] & raw[b]
    # Require the enumerator to recover a deliberately altered output gate.
    baseline, out = star(edges[1:])
    _, a,b = baseline[-1]
    values = list(raw)
    for op,i,j in baseline[:-1]:
        values.append(values[i] & values[j] if op == 'and' else values[i] | values[j])
    altered = values[a] & values[b]
    assert (112, 'and', min(a,b), max(a,b)) in set(survivors(baseline,out,raw,altered,full))
    total = 0
    for oriented in (edges, [(b,a) for a,b in edges]):
        for dropped in oriented:
            gates,out = star([edge for edge in oriented if edge != dropped])
            for candidate in survivors(gates,out,raw,target,full):
                print('survivor',dropped,candidate,flush=True)
                total += 1
    print('gate replacements surviving:',total,'circuits:',2*len(edges),'tests:',len(tests))
if __name__ == '__main__':
    main()
