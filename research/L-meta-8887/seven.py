"""Enumerate all labeled extremal incidence tables up to permutations of the rows."""
from itertools import combinations, permutations
from collections import Counter
from math import factorial
from pathlib import Path
import json
points=range(7)
pairs=list(combinations(points,2))
triples=list(combinations(points,3))
covered={t:frozenset(combinations(t,2)) for t in triples}
def complete(unused, lines):
    if not unused:
        yield tuple(sorted(lines))
        return
    pivot=min(unused)
    for t in triples:
        if pivot in covered[t] and covered[t] <= unused:
            yield from complete(unused-covered[t],lines+[t])
catalogue=list(complete(frozenset(pairs),[]))
assert len(catalogue)==len(set(catalogue))==30
canonical=tuple(t for t in triples if (t[0]+1)^(t[1]+1)^(t[2]+1)==0)
def image(system,perm):
    return tuple(sorted(tuple(sorted(perm[i] for i in t)) for t in system))
orbits=Counter(image(canonical,p) for p in permutations(points))
assert set(orbits)==set(catalogue) and set(orbits.values())=={168}
def matching_count(table):
    return sum(all(p[i] in row for i,row in enumerate(table)) for p in permutations(points))
counts={matching_count(s) for s in catalogue}
assert counts=={24}
summary={'column_labeled_row_unordered':len(catalogue),'fully_labeled':len(catalogue)*factorial(7),'automorphisms_preserving_sides':168,'perfect_matchings_per_table':24}
print(json.dumps(summary,sort_keys=True))
