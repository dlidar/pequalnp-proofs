"""Independent packed truth-table replay. Bit position is the 24-bit input mask."""
from collections import Counter
from edits import star_circuit
from mcgee import E,V
from functools import reduce
from operator import or_
import json

def main():
    # Evaluate blocks of 65,536 rows to bound peak memory.
    counts = [0]*len(E)
    gates = [star_circuit(E[:i]+E[i+1:]) for i in range(len(E))]
    full = star_circuit(E)
    def evaluate(network,cols):
        w = cols.copy()
        for op,a,b in network:
            w.append((w[a] & w[b]) if op=='and' else (w[a] | w[b]))
        return w[-1]
    block = 1<<16
    ones = (1<<block)-1
    fixed = []
    for i in range(16):
        run = 1<<i
        half = (1<<run)-1
        fixed.append((ones//((1<<(2*run))-1))*(half<<run))
    for high in range(256):
        cols = fixed + [ones if high >> j & 1 else 0 for j in range(8)]
        y = reduce(or_,(cols[a]&cols[b] for a,b in E))
        assert evaluate(full,cols)==y
        for i,network in enumerate(gates):
            got = evaluate(network,cols)
            assert not (got & ~y)
            counts[i] += (y ^ got).bit_count()
    return dict(inputs=block*256,full_gates=len(full),full_errors=0,
                deletion_false_positives=0,deletion_false_negatives=dict(sorted(Counter(counts).items())))
if __name__=='__main__':
    print(json.dumps(main(),indent=2))
