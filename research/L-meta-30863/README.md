# Universal inverter replacements for L-meta-30863

The assignment compares the minimum sizes of circuits for an eight-vertex graph with and without one NOT. General internal sharing remains open. These are research results.

## Exact substitution criterion

Let F be a monotone Boolean function, g an arbitrary Boolean signal, and b a monotone proposed replacement for its complement. Every monotone decoder D that computes F from the raw input x and the additional input NOT g(x) continues to compute F after replacing that input by b(x) if and only if both tests below pass.

* On each minimal true input p of F with g(p)=0, b(p)=1.
* On each maximal false input n of F with g(n)=1, b(n)=0.

The decoder may use its extra bit arbitrarily often. For sufficiency, monotonicity extends the checks from the two boundaries. For necessity, if a positive test at p fails, use the decoder F(x) AND (y OR [x is not below p]). At an offending negative test use F(x) OR (y AND [x is above n]). Repair.lean and Necessity.lean prove both directions. Boundary.lean and AllTraces.lean give the exact 14 minimal positives and eight maximal negatives of the assigned graph. All 22 form a single antichain, so every one of the 4,194,304 traces on them is realized by a monotone signal.

## Exact formula prices

For every trace we computed the minimum number of raw input leaves in a monotone replacement formula satisfying the criterion. Constants cost zero. An OR root partitions the required positive examples and an AND root partitions the required negative examples. profiles.cpp fills the 4,194,304-entry table. checkprofiles.cpp independently checks every atomic boundary, every partition inequality and an attaining split or leaf for every entry. A binary monotone formula for the full graph needs 15 leaves (14 gates), attained by Reference.lean.

Among 7,966 distinct boundary traces first realized with at most four monotone gates, precisely one requires a 15-leaf replacement. The signal is
`(x0 AND x2) OR (x4 AND (x5 OR x7))`.
No trace realized with at most three gates requires more than 13 leaves. catalog.py identifies the reachable boundary states by sets of available signals; census.cpp independently enumerates straight-line histories, including repeated signals. Across all realizable traces, 242 require 15 leaves.

For this four-gate signal the replacement must accept all 14 edge pairs and reject the five masks 7, 21, 56, 112 and 144. For each of the eight coordinates there are a required positive and a required negative that obstruct dropping that coordinate. Thus every monotone replacement depends on all eight inputs. A fan-in-two circuit with k gates depends on at most k+1 inputs, giving at least seven gates even when the replacement has unrestricted sharing. This lower bound concerns a single replacement that works for every decoder. It does not settle conversion of a particular circuit.

A counting argument improves seven to nine for shared monotone gates. Prune unused gates and simplify constants and unary gates. A connected circuit with eight essential inputs and k binary gates has 2k+1 uses including its output and at least 8+k different wires to use. At k≤8 there is at most one extra use. With no reused gate output, the circuit unfolds to a formula with at most nine leaves. Otherwise a single gate output z is used twice, and every raw input is used exactly once. If its input tree contains u gates, unfolding adds u gates, giving k+u+1 leaves. The checked 15-leaf minimum forces u≥6, so the tree uses at least seven distinct inputs. The remaining monotone decoder thus sees z and at most one raw variable t. With no other variable the function is z; this has at most nine leaves. With one other essential variable the decoder must be AND or OR of z and t, the only two monotone Boolean functions depending on both arguments. For each t there is a required positive omitting it and a required negative containing it. Canalyzing.lean verifies these tests and excludes both possibilities. The counting argument combines the independently checked formula minimum and the kernel-checked finite tests.

## Shared products and nearly exact circuits

For shared OR preprocessing followed by complete bipartite AND products and a final OR, the graph costs exactly 14 gates. The universal replacement for the four-gate signal costs exactly 12 gates in this model. Only three additional edges avoid all five forbidden masks. rectbound.cpp enumerates covers by legal products, pruning with one gate for every distinct nontrivial operand set and 2k−1 gates for k products and their output OR. Only 953 covers survive the 13-gate cutoff for the original graph. For the replacement problem 123,108 covers survive it. budget.py and partial.py exhaust the remaining possible OR constructions by splitting required unions into arbitrary overlapping proper subsets. A 12-gate witness is in partial-min.json.

Two 13-gate monotone circuits for the assigned graph each have a single error on its 256 inputs. The first accepts the extra mask 66 (vertices 1 and 6). The second misses mask 130 (vertices 1 and 7). OneError.lean checks both directly against the assigned predicate. two.cpp exhausts 4,286,165 alternatives for each circuit obtained by replacing one or two gates in its fixed order, allowing one NOT. None is exact. The 14-gate monotone circuit remains the unrestricted upper bound established here.

Run `bash verify.sh /path/to/pequalnp-proofs/lean` in a checkout with the project's Lean 4.36.0 dependencies built. The general substitution theorem and explicit constructions are Lean results. The exhaustive formula prices, prefix census, product minima and bounded repair searches are independent integer computations.
