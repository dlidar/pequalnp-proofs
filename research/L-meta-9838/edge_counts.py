"""Count changes to the edge function on deleting one edge; two independent orientations."""
import json
from pathlib import Path
from collections import Counter

def losses(edges):
    neighbors = {}
    for i, j in edges:
        neighbors.setdefault(i, set()).add(j)
    columns = set.union(*neighbors.values())
    answer = {}
    for i, j in edges:
        # Set both endpoints true. All their other neighbors must be false.
        left = sorted(k for k in neighbors if j not in neighbors[k])
        right = sorted(columns - neighbors[i])
        masks = [sum(1 << b for b, v in enumerate(right) if v in neighbors[k]) for k in left]
        # Count the independent extensions. Overlaps in the same mask are intentional.
        counts = Counter({0: 1})
        for mask in masks:
            added = Counter()
            for used, multiplicity in counts.items():
                added[used | mask] += multiplicity
            counts.update(added)
        answer[i, j] = sum(n * (1 << (len(right) - used.bit_count())) for used, n in counts.items())
    return answer

if __name__ == "__main__":
    edges = json.loads(Path(__file__).with_name("edges.json").read_text())
    forward = losses(edges)
    backward = losses([(j, i) for i, j in edges])
    assert all(count == backward[j, i] for (i, j), count in forward.items())
    print(sorted(Counter(forward.values()).items()))
    best = min(forward.values())
    print(best, sorted(edge for edge in forward if forward[edge] == best))
