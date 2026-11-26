"""Generate and integer-check a signed rectangle certificate for every two-bit lookup.

Requires NumPy and SciPy. The row/column order matches the five-vertex triangle assignment.
The linear program proposes weights. Only the final integer tests establish the bound.
"""
import itertools
import json
import sys
import numpy as np
from scipy.optimize import linprog

EDGES = list(itertools.combinations(range(5), 2))
TERMS = [sum(1 << EDGES.index(e) for e in itertools.combinations(t, 2))
         for t in itertools.combinations(range(5), 3)]
PERMS = [[EDGES.index(tuple(sorted((p[u], p[v])))) for u, v in EDGES]
         for p in itertools.permutations(range(5))]

def rename(row, perm):
    return sum(1 << perm[i] for i in range(10) if (row >> i) & 1)

def rectangle_max(matrix, weight):
    """Enumerate all subsets of the smaller side and maximize over the opposite side."""
    best = 0
    chosen = None
    d = matrix.shape[0]
    for lo in range(0, 1 << d, 2048):
        ns = np.arange(lo, min(lo + 2048, 1 << d))[:, None]
        bits = ((ns >> np.arange(d)) & 1).astype(weight.dtype)
        sums = bits @ weight[matrix]
        values = np.maximum(0, sums).sum(axis=1)
        i = int(values.argmax())
        if values[i] > best:
            best = values[i]
            chosen = matrix[np.ix_(bits[i].astype(bool), sums[i] > 0)]
    return best, chosen

def certify(a, b):
    def target(r):
        return any(r & t == t for t in TERMS)
    maximal = [r for r in range(1024) if not target(r)
               and all(target(r | (1 << i)) for i in range(10) if not r >> i & 1)]
    pins = [0, 1 << a, 1 << b, (1 << a) | (1 << b)]
    rows = sorted({r | p for r in TERMS for p in pins})
    cols = sorted({r & ~p for r in maximal if r.bit_count() == 6 for p in pins})
    assert all(map(target, rows)) and not any(map(target, cols))
    group = [g for g in PERMS if {g[a], g[b]} == {a, b}]
    ids = {}
    for r in rows:
        for c in cols:
            if (r,c) not in ids:
                k = max(ids.values(), default=-1) + 1
                ids.update({(rename(r,g), rename(c,g)): k for g in group})
    matrix = np.array([[ids[r,c] for c in cols] for r in rows])
    n = matrix.max() + 1
    counts = np.bincount(matrix.ravel(), minlength=n)
    tests = [lambda r,i=i: (r >> i) & 1 for i in range(10)]
    tests.extend(lambda r,s=s: (s >> (((r >> a) & 1) + 2*((r >> b) & 1))) & 1
                 for s in range(1,15))
    views = []
    for f in tests:
        m = matrix[np.ix_([bool(f(r)) for r in rows], [not f(c) for c in cols])]
        views.append(m if m.shape[0] <= m.shape[1] else m.T)
    constraints = list(np.eye(n))
    for _ in range(400):
        res = linprog(-counts, A_ub=constraints, b_ub=np.ones(len(constraints)),
                      bounds=(-2,1), method='highs')
        assert res.success
        w = res.x
        more = []
        for view in views:
            best, rect = rectangle_max(view, w)
            if best > 1 + 1e-7:
                more.append(np.bincount(rect.ravel(), minlength=n))
        if not more:
            break
        constraints.extend(more)
    else:
        raise RuntimeError("No certificate found within the cut limit")
    cap = 100000
    coeff = np.floor(w*cap + 1e-8).astype('int64')
    assert all(rectangle_max(m, coeff)[0] <= cap for m in views)
    total = int(counts @ coeff)
    assert total > 21*cap
    return dict(pins=[a,b], rows=rows, cols=cols, cap=cap, total=total, weight=coeff[matrix].tolist())

if __name__ == '__main__':
    print(json.dumps(certify(0, int(sys.argv[1])), separators=(',',':')))
