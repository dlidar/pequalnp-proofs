"""Enumerate all maximal negative inputs on the posted order-four incidence graph."""

from collections import Counter

ORDER = 21
ALL = (1 << ORDER) - 1
OFFSETS = (20, 0, 5, 7, 17)


def classify_from_points():
    """Scan every point subset, retaining those equal to their double closure."""
    rows = tuple(sum(1 << ((p + k) % ORDER) for k in OFFSETS) for p in range(ORDER))
    neighborhoods = [0] * (1 << ORDER)
    for pset in range(1, 1 << ORDER):
        bit = pset & -pset
        neighborhoods[pset] = neighborhoods[pset ^ bit] | rows[bit.bit_length() - 1]
    # The largest preimage is precisely the union of all preimages.
    closed = {}
    for pset, neighborhood in enumerate(neighborhoods):
        closed[neighborhood] = closed.get(neighborhood, 0) | pset
    return {(pset, ALL ^ neighborhood) for neighborhood, pset in closed.items()}


def classify_from_lines():
    """Build every intersection of allowable point sets, then complete the line side."""
    avoids = [sum(1 << p for p in range(ORDER) if (l - p) % ORDER not in OFFSETS)
              for l in range(ORDER)]
    point_sets = {ALL}
    for compatible in avoids:
        point_sets |= {p & compatible for p in point_sets}
    return {(p, sum(1 << l for l, compatible in enumerate(avoids) if p & ~compatible == 0))
            for p in point_sets}


def main():
    masks = classify_from_points()
    assert masks == classify_from_lines()
    costs = Counter(41 - p.bit_count() - l.bit_count() for p, l in masks)
    expected = {20: 2, 24: 42, 27: 420, 29: 2408, 30: 5460, 31: 16800, 33: 105}
    assert costs == expected
    assert sum(costs.values()) == 25237
    for cost, count in sorted(costs.items()):
        print(cost, count)


if __name__ == "__main__":
    main()
