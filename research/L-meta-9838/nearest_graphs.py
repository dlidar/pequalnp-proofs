"""Hamming distance to any other simple graph function on the same 40 inputs.

For an added edge, count the old independent sets containing both its endpoints.
For a removed edge, delete it first and count independent sets containing both.
These errors persist if further edges of the same kind are added or removed.
Any mixed edit has at least the errors forced by each single added edge.
"""
import json
from collections import Counter
from itertools import combinations
from functools import cache
from pathlib import Path

def changes(vertices, pair, left, right):
    selected = set(pair)
    forbidden = set()
    for u in selected:
        forbidden.update(vertices[u] - selected)
    rows = sorted(left - selected - forbidden)
    columns = sorted(right - selected - forbidden)
    counts = Counter({0: 1})
    for u in rows:
        mask = sum(1 << j for j,v in enumerate(columns) if v in vertices[u])
        add = Counter()
        for old, mult in counts.items():
            add[old | mask] += mult
        counts.update(add)
    return sum(n << (len(columns)-mask.bit_count()) for mask,n in counts.items())

if __name__ == '__main__':
    edges = {tuple(x) for x in json.loads(Path(__file__).with_name('edges.json').read_text())}
    vertices = {v:set() for v in range(40)}
    for u,v in edges:
        vertices[u].add(v)
        vertices[v].add(u)
    left, right = set(range(20)), set(range(20,40))
    # Independent graph recurrence, with a common cache across all edits.
    adjacency = [sum(1 << k for k in vertices[i]) for i in range(40)]
    @cache
    def independent_sets(active):
        if not active:
            return 1
        bits = [i for i in range(40) if active >> i & 1]
        pivot = max(bits, key=lambda i: (adjacency[i] & active).bit_count())
        if not adjacency[pivot] & active:
            return 1 << len(bits)
        others = active ^ (1 << pivot)
        return independent_sets(others) + independent_sets(others & ~adjacency[pivot])
    changes_by_kind = {'deletion':{}, 'addition':{}}
    for pair in combinations(range(40),2):
        n = changes(vertices, pair, left, right)
        assert n == changes(vertices, pair, right, left)
        i,j = pair
        excluded = (1 << i) | (1 << j) | adjacency[i] | adjacency[j]
        assert n == independent_sets(((1 << 40) - 1) & ~excluded)
        changes_by_kind['deletion' if pair in edges else 'addition'][pair] = n
    for kind, costs in changes_by_kind.items():
        minimum = min(costs.values())
        print(kind, len(costs), sorted(Counter(costs.values()).items()))
        print('minimum', minimum, 'attained at', [k for k,v in costs.items() if v == minimum])
