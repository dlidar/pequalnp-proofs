# Circuits for four-cycle-free bipartite graphs with a perfect matching

L-meta-8887 asks for at least |E| + n − 1 gates when both sides have n vertices of degree at least three. The unrestricted inequality remains open.

Child.lean proves the exact first child of the reduction in upstream PR #38392. A perfect matching ensures that all 2n input wires affect the incidence function. An unused gate can be removed and later wire numbers shifted while preserving evaluation, binary fan-in and backward references. Iterating gives an equivalent circuit no larger in which every gate and every raw wire is read or designated as the output. The proof allows repeated gate operands. Prune.lean adapts the wire and deletion arguments of upstream L_lib_376. Residual.lean applies the original reduction with that child discharged. The remaining hypothesis bounds edges beyond a matching by the number of repeated wire uses.

Packing.lean counts the other rows accessible through each column incident with a fixed row. Four-cycle-freeness makes these sets disjoint, so the sum of their sizes is at most n−1. Minimum degree three implies n≥7 whenever a row exists and gives the posted conclusion at n≤6. At n=7 every row has degree three and every two distinct rows share exactly one column. Dual statements follow by exchanging the sides.

The independent integer enumeration in seven.py chooses the first uncovered pair of columns and tests each compatible triple containing it. It compares the resulting tables against all 5040 column permutations of the binary Fano plane. Exactly 30 systems occur with row order suppressed, or 151200 with both sides labeled. Each has 168 side-preserving automorphisms and 24 perfect matchings. This identifies the first remaining order with the Fano problem of excluding circuits of at most 26 gates.

Run bash verify.sh from a checkout of the fork and python3 seven.py for the independent enumeration.
