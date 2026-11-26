"""Exhaust the eight-gate search for graph mask 1534 on the one-each promise.

The soundness argument for reachable live wire sets is checked in Core.lean,
adapted from the upstream proof of L-meta-5469. Raw words record ordered
positive/negative pairs. A live set must distinguish every such pair.
"""
from itertools import combinations, product

rows = range(15)
positive = [r for r in rows if (1534 >> r) & 1]
negative = [r for r in rows if not (1534 >> r) & 1]
pairs = list(product(positive, negative))
width = len(pairs)
full = (1 << width) - 1
goal = full << width
samples = [n for _, n in pairs] + [p for p, _ in pairs]
raw = tuple(sum(1 << bit for bit, r in enumerate(samples)
                if wire in (r // 5, r % 5 + 3)) for wire in range(8))


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
    starts = [s for n in range(9) for s in combinations(raw, n) if separates(s)]
    assert starts == [raw]
    assert not any(attainable(s, 9 - len(s), 8) for s in starts)
    print('No circuit of at most eight gates on the 15 promised inputs.')
