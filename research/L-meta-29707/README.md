# One inverter in an unshared formula for L-meta-29707

The minimum is **14 gates** for both monotone formulas and formulas using AND, OR and at most one NOT. A binary AND or OR and a unary NOT each cost one gate. The assigned statement concerns circuits with unrestricted sharing. Its truth remains open in this work.

The upper bound is a 14-gate monotone formula on the posted eight variables. Each non-output internal wire has exactly one reader. Reference.lean verifies the circuit against the posted graph predicate on all 256 inputs.

## Eliminating an inverter in a small decoder

Write a formula with one NOT as a monotone context with one hole holding the negation of a monotone formula. If the latter has k leaves and the context has d leaves including the hole, the total gate count is k+d−1. Constants and unary AND/OR gates can first be simplified. A putative 13-gate formula has k+d≤14.

Consider the path from the hole to the output. Let P be the variables occurring in the siblings of the AND nodes, and Q the variables occurring in the siblings of the OR nodes. The hole affects the output precisely when every AND sibling is true and every OR sibling is false. Throughout this region the output equals the antitone signal in the hole. A monotone output and an antitone signal agreeing there have equal values at any two comparable points of the region.

To compare inputs, first set P-only coordinates to true, then set coordinates outside P to false. Both moves stay in the region. The resulting input depends on the original input only through P∩Q. If that intersection contains at most two variables, its two-bit patterns with different output labels must be incomparable. The only incomparable pair in the two-dimensional Boolean cube is 01 and 10. A constant or one of the coordinates therefore agrees with the desired output throughout the region. Substituting that signal in the hole and folding constants gives a monotone formula with at most d leaves.

Every essential variable occurs outside the inverter. Otherwise the entire result is antitone in that variable. Variables in P∩Q occur at least twice outside the inverter. This gives d≥1+n+|P∩Q| for n essential variables. Bridge.lean, Context.lean, Leaves.lean and Convert.lean give a general kernel-checked conversion for d≤n+3. Graph.lean checks all eight inputs are essential and specializes the conversion. If k≥3 then d≤11. The resulting monotone formula would have at most 11 leaves.

## Independent finite lower bounds

The twelve minimal positive and seven maximal negative graph inputs suffice for a monotone decoder. A separating potential on all 524,288 pairs of subsets gives 15 at the full pair. checkprofiles.cpp checks the value at every legal leaf and every binary partition inequality independently of the producer. Induction on the formula proves the bound. At an AND root partition the negative rows according to a rejecting operand, and at an OR root partition the positive rows according to an accepting operand. Thus every monotone formula requires at least 15 leaves.

It remains to check the one- and two-leaf inverter inputs. These are eight variables, 28 distinct conjunctions and 28 distinct disjunctions. Repeated identical operands simplify to a variable. Write h for the uninverted subformula. Pinning its complement to zero preserves correctness on positive rows with h=1 and keeps every negative row rejected, by monotonicity of the context in the hole. Pinning to one works on all positive rows and on negative rows with h=0. Folding a pinned hole in either case saves at least one leaf in the nontrivial context. The separating potential directly certifies 27 of the 64 cases.

For the other 37 cases small-certs.json gives 32 signed integer matrices on actual positive and negative inputs. A separating formula partitions their Cartesian product into leaf rectangles. Each such rectangle lies in the region where the corresponding signal is true on the positive side and false on the negative side. checksmall.py enumerates every subset on the smaller side of this rectangle, selecting all positive-sum columns on the other side to obtain its exact maximum weight. For each of the 37 cases, total weight exceeds (14−k) times every single-leaf maximum, even when the decoder may reuse the complemented signal. Hence d≥15−k. Together with the structural conversion this rules out every unshared formula with at most 13 gates and at most one inverter.

## Additional shared models

For a single preliminary binary AND or OR of distinct raw variables and an unshared monotone decoder that may reuse that signal, all 56 cases have total cost 14 or 15. Two ANDs and sixteen ORs achieve 14. The two AND choices are (0,4) and (1,5). A separate exact search covers circuits with shared OR preprocessing, complete bipartite products and a final OR. It finds minimum 14 over 66 available products. These calculations permit the indicated sharing patterns.

Run `bash verify.sh /path/to/pequalnp-proofs/lean` with the project's Lean 4.36.0 dependencies built. The axiom audit covers the general conversion, its specialization, the witness and the signed-weight argument. The graph-specific separating potential, small-inverter certificate replay and shared-model searches use independent integer computation outside Lean.

## Dependence on the number of mixed coordinates

The same anchoring argument reduces the choice of a replacement to a finite interpolation problem for any number of mixed coordinates. Oppositely labeled points in the remaining cube must be incomparable. For every possible set of zero labels, the most demanding legal set of ones consists of every point incomparable with all those zeros. The exact worst replacement costs on cubes of dimension 1, 2, 3 and 4 are respectively 0, 1, 2 and 5 leaves, counting constants as free. cube.py enumerates the 3, 6, 20 and 168 monotone Boolean functions with their exact minimum costs and exhausts all zero-label sets. For four coordinates the zero masks {3,5,9} and one masks {6,10,12,14} require five leaves. On three coordinates, Three.lean verifies that a constant, one input or a single binary gate always suffices, and exhibits a case needing the binary gate.
