"""Count truth-table disagreements after every single edge edit of L-meta-9811."""
from collections import Counter
from itertools import combinations

EDGES = {
    (0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13),
    (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
    (5, 10), (5, 12), (6, 8), (6, 9), (6, 11),
}
VERTICES = set(range(14))


def enumerate_distances():
    distances = Counter()
    masks = {edge: (1 << edge[0]) | (1 << edge[1]) for edge in EDGES}
    for assignment in range(1 << len(VERTICES)):
        present = [edge for edge, mask in masks.items() if assignment & mask == mask]
        if len(present) == 1:
            distances[present[0]] += 1
        elif not present:
            active = [v for v in sorted(VERTICES) if assignment & (1 << v)]
            distances.update(combinations(active, 2))
    return distances


def independent_set_count(vertices, edges):
    if not edges:
        return 1 << len(vertices)
    pivot = min(edges)[0]
    neighbors = {v for e in edges if pivot in e for v in e if v != pivot}
    without = vertices - {pivot}
    reduced = {e for e in edges if pivot not in e}
    return independent_set_count(without, reduced) + independent_set_count(
        without - neighbors, {e for e in reduced if neighbors.isdisjoint(e)}
    )


def count_with_fixed_endpoints(pair):
    other_edges = EDGES - {pair}
    forced_off = {v for e in other_edges if set(pair).intersection(e) for v in e}
    free = VERTICES.difference(pair, forced_off)
    return independent_set_count(free, {e for e in other_edges if free.issuperset(e)})


if __name__ == "__main__":
    distances = enumerate_distances()
    pairs = set(combinations(sorted(VERTICES), 2))
    assert all(distances[pair] == count_with_fixed_endpoints(pair) for pair in pairs)
    for label, family, expected, minimizers in [
        ("delete", EDGES, 47, {(5, 10), (6, 8)}),
        ("add", pairs - EDGES, 18, {(3, 13), (6, 10), (5, 8)}),
    ]:
        best = min(distances[e] for e in family)
        achieving = {e for e in family if distances[e] == best}
        assert (best, achieving) == (expected, minimizers)
        print(label, best, sorted(achieving))
