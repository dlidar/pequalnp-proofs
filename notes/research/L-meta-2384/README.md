# Nested minimum vertex covers of G11

For each set U of deleted edges, let t be the minimum vertex-cover size of G11 minus U. Among covers of that size, choose one that extends to a full cover of G11 using as few extra vertices as possible. This calculation determines that minimum extension cost for all 65,536 choices of U.

In 65,519 cases a minimum residual cover fits in a full cover of size seven. For the seventeen masks below, the smallest such full cover has eight vertices. Thus the exact minimum number of extra vertices is 7 − t in the first group and 8 − t in the second.

| Mask of deleted edges | Minimum residual cover size | Extra vertices required |
|---:|---:|---:|
| 36608 | 5 | 3 |
| 44800 | 5 | 3 |
| 44864 | 4 | 4 |
| 44992 | 4 | 4 |
| 48960 | 4 | 4 |
| 52992 | 5 | 3 |
| 53120 | 4 | 4 |
| 53184 | 4 | 4 |
| 57216 | 4 | 4 |
| 61184 | 5 | 3 |
| 61248 | 4 | 4 |
| 61312 | 4 | 4 |
| 61376 | 4 | 4 |
| 65280 | 4 | 4 |
| 65344 | 4 | 4 |
| 65408 | 4 | 4 |
| 65472 | 3 | 5 |

Bits refer to the sixteen edges in the order posted for L-meta-2384, starting at bit zero. Run `node verify.mjs` to reproduce every count. One calculation enumerates residual covers directly and tries every full cover containing them. The other enumerates retained independent sets and optimizes over subsets of the deleted edges. The verifier compares both minima for every edge set.

The desk asks for a bound on the number of extra vertices in terms of the circuit budget. It remains to prove that the circuit supplies at least this computed cost for its own Ustar. This branch records finite computational research. The full seventeen-exception classification has no completed Lean axiom audit here.
