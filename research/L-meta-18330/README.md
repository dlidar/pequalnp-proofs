# Fano incidence with shared input gates

L-meta-18330 asks for a monotone circuit with at most 25 gates on the 14 point and line inputs. Its 21 positive flags and the 37 maximal negative inputs determine the function by monotonicity. Reference.lean checks an ordinary 27-gate circuit against the posted tests, including distinct earlier operands.

## One shared preprocessing gate

The smallest unshared decoder formula has 27 leaves when the extra signal is the OR of two points or of two lines, and 28 leaves for every other AND or OR of two distinct raw inputs. Exactly 42 of the 182 choices save a leaf. The full cost with one preprocessing gate is therefore at least 27 gates, attained by a star construction. Exact.lean checks the matching upper and lower bounds for every choice. Transport.lean checks the symmetries taking all 182 gates to the six representatives.

The lower certificate gives integer weights to pairs consisting of a positive and a maximal negative input. At an AND node a separating formula partitions the negative inputs, and at an OR node it partitions the positive inputs. A leaf can only receive positive inputs on which it is true and negatives on which it is false. Summing the maximum leaf mass over this partition bounds the formula size. For each eligible subset of positive inputs, all eligible columns with positive total weight give the maximum mass. FormulaMass.lean is reused from the fork's L-meta-9815 research at 19f37a7ac46506f2a9982fdd3a19b55c7e6f6ea4.

## Two preprocessing gates

Each gate may read any two distinct earlier wires. The decoder has all fourteen raw inputs and both computed signals. All 38,220 ordered programs fall into 260 orbits under 336 verified incidence symmetries. Every orbit has an integer certificate requiring at least 26 decoder leaves. Two preprocessing gates and an unshared decoder therefore require at least 27 gates. Two disjoint same-side ORs replacing two different pairs of leaves in the seven line stars attain 27. The two-signal lower bound is checked by a standalone integer verifier.

## Free monotone signals on any three inputs

Even if every monotone function of the three specified raw inputs is supplied to the decoder at no cost, the exact decoder leaf counts are as follows.

| Triple | Choices | Leaves |
|---|---:|---:|
| Same side, three inputs with no common neighbor | 56 | 25 |
| Same side, three inputs with a common neighbor | 14 | 26 |
| Mixed point and line inputs | 294 | 27 |

The integer verifier considers all 20 monotone truth tables on three bits and checks each lower certificate. The matching expression combines the free OR of each star's inputs inside the triple with the remaining raw inputs of that star. The decoder then forms the star products and joins them by OR. Consequently preprocessing confined to any three inputs also requires 27 total gates. With at least three preprocessing gates the decoder needs at least 24 more, and the results above cover zero, one and two preprocessing gates.

Run `bash verify.sh` from this directory in the fork checkout based on 624acb3fb2189a78719c262c1af407bd73fb3b5c. The script builds the Lean 4.36.0 sources and audits their axioms. It then runs the independent integer checks for two gates and three-input scopes. The unrestricted 25-gate existence question remains open in this research.

The file nearest.json contains a 25-gate approximation with 68 false negatives and 18 false positives across all 16,384 inputs. The independent verifier recomputes each output and checks the gate operands.
