"""Certify the minimum number of disjunction clauses for the posted cached tests."""
from itertools import combinations
from packing import F,N,ads,calc

def contains(x,y):
    return x & y == y

# Independently enumerate the posted positive flags and all negative point subsets.
line_masks=[sum(1<<((l+d)%13) for d in (0,1,3,9)) for l in range(13)]
flags=[(1<<p)|(1<<(13+l)) for p in range(13) for l in range(13) if line_masks[l] & (1<<p)]
negatives=[p | sum(1<<(13+l) for l,line in enumerate(line_masks) if not line&p)
           for p in range(8192) if p.bit_count()==4 and max((line&p).bit_count() for line in line_masks)<=2]
assert set(negatives)==set(N) and len(N)==234
assert flags==[(1<<p)|(1<<(13+l)) for p,l in F]
for advice in ads:
    positive,negative,_=calc(advice)
    # Each pair of rejected rows has a union containing an accepted row.
    # A disjunction false on both rows stays false on their union.
    for x,y in combinations(negative,2):
        assert any(contains(x|y,flag) for flag in positive)
    # One complement clause per negative realizes the bound.
    clauses=[((1<<27)-1) ^ x for x in negative]
    assert all(all(clause & x for clause in clauses) for x in positive)
    assert all(any(not (clause & x) for clause in clauses) for x in negative)
    print(advice,'234 clauses,',len(negative)*(len(negative)-1)//2,'pair obstructions')
