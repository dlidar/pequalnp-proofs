# A single shared gate in the 14-input graph of L-meta-9815

The desk asks whether every unrestricted AND/OR/NOT circuit for this graph needs at least 25 gates. A 25-gate monotone circuit is displayed in `Upper.lean`. The unrestricted 24-gate question remains open.

For a binary monotone formula on the original inputs, the exact minimum is **26 leaves**, hence 25 gates. Giving the formula one extra literal equal to the complement of any raw input preserves that minimum. These results and the explicit ordinary circuit were checked in pinned Lean 4.36.0.

For a single extra literal equal to an AND or OR of two distinct inputs, the exact formula minimum depends on the choice of input pair.

| Extra literal | Choices | Minimum decoder leaves |
|---|---:|---:|
| OR of two vertices with a common neighbor | 34 | 25 |
| Any other OR of two vertices | 57 | 26 |
| AND of two vertices | 91 | 26 |

In each of the 34 useful cases, take the star of a common neighbor and form the OR of the two specified inputs first. Count the supplied gate and the smallest resulting circuit in this model still has 25 gates. With identical operands, the extra literal repeats a raw input.

The independent verifier in `verify.py` checks all integer certificates in `weights.json.gz`. For each test pair it uses one of 19 positive edge inputs and one of 36 maximal independent sets. Each formula leaf identifies a rectangle of pairs distinguished by that literal. The verifier checks every subset of eligible positive rows and sums the positive column totals, giving an upper bound valid for every allowed choice of columns. The signed matrix mass divided by this cap bounds the number of leaves. For a complemented literal, the verifier also bounds its rectangle by the sum of the positive entries over all eligible pairs. Every upper witness for the 34 useful caches is independently tested on all 16,384 inputs.

Pinned Lean 4.36.0 checked this classification and all 251 named research theorems passed the permitted-axiom audit. Run `bash check.sh` here for the independent integer verifier and ordinary and complemented-input Lean bounds. Run `bash replay/check.sh` for the full binary-gate classification and axiom audit.

The unrestricted 24-slot circuit search returned UNKNOWN after twenty minutes. Shared intermediate gates and internal negations remain open.
