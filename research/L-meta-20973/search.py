"""Exhaust the eight-gate search for graph mask 241139 on the one-each promise.

The soundness argument for reachable live wire sets is checked in Lower.lean,
adapted from the upstream proof of L-meta-5469. Raw words record ordered
positive/negative pairs. A live set must distinguish every such pair.
"""
from itertools import combinations, product

rows = range(20)
positive = [r for r in rows if (241139 >> r) & 1]
negative = [r for r in rows if not (241139 >> r) & 1]
pairs = list(product(positive, negative))
width = len(pairs)
full = (1 << width) - 1
goal = full << width
samples = [n for _, n in pairs] + [p for p, _ in pairs]
raw = tuple(sum(1 << bit for bit, r in enumerate(samples)
                if wire in (r // 5, r % 5 + 4)) for wire in range(9))


def separates(wires):
    cuts = 0
    for word in wires:
        cuts |= (word >> width) & ~word
    return (cuts & full) == full


def continuations(wires, spare):
    for i, j in combinations(range(len(wires)), 2):
        a, b = wires[i], wires[j]
        rest = tuple(x for k, x in enumerate(wires) if k not in (i, j))
        for w in (a & b, a | b):
            for keep in ((), (a,), (b,), (a, b)):
                if len(keep) <= spare:
                    next_wires = (w,) + keep + rest
                    if separates(next_wires):
                        yield next_wires, spare - len(keep)


def attainable(wires, spare, gates):
    if wires == (goal,):
        return True
    return gates > 0 and any(attainable(w, d, gates - 1)
                             for w, d in continuations(wires, spare))


if __name__ == '__main__':
    starts = [s for n in range(10) for s in combinations(raw,n) if separates(s)]
    assert starts == [raw]
    assert not attainable(raw,0,8)
    assert [i for i in range(9) if attainable(raw+(raw[i],),0,9)] == [1]
    print("Minimum nine gates by Lower.lean and Upper.lean. Only left input 1 can repeat in a ten-leaf formula.")
