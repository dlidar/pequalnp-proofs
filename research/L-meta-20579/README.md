# L-meta-20579, shard 63

The posted target has 411 positive cells among the 1,024 inputs with one row and one column selected. A qualifying inverter reads the output of an earlier gate. Shard 63 requires its first such inverter to be true on all six diagonal inputs from (0,0) through (5,5).

## Mixed OR operands

The least number of products in an OR of products of two ORs of raw inputs is 15. Products.lean evaluates the construction on all 1,024 cells. The OR gates used to build its operands are charged in the original problem.

For the lower bound, each operand has a row set and a column set. Two operands in a sound product have disjoint row sets, since a row in both would make that entire row positive. Their column sets are disjoint for the same reason. The product therefore contributes at most two all-positive rectangles. A 335-node branching certificate proves that 28 rectangles cannot cover the graph. The checker enumerates all 1,893 inclusion-maximal all-positive rectangles and branches on whether to use one. Each leaf gives nonnegative integer weights on still-uncovered cells. The total exceeds the remaining rectangle budget times the largest weight of any available rectangle. Extending a rectangle to a maximal one preserves soundness and coverage. Run `python check_rectangles.py` to check both the lower bound and the paired construction.

## Fixed operand sets

The file `terms` gives the 32 OR operand masks of the upstream 180-gate reference L-meta-20578, with its original pairing. Computing those same union masks by shared binary OR gates costs at least 143 gates. Including the 16 products and the final 15 binary ORs gives a lower bound of 174 for that construction. This lower bound concerns exact operand unions over the raw inputs.

In an OR circuit, a wire's support is the union of its predecessors' supports. A wire feeding two different requested outputs has support contained in their intersection. Keep the raw inputs, all such shared supports, and the requested outputs. Every other useful wire reaches a single requested output. Its portion of that output's fan-in graph can be replaced by one union of the distinct retained boundary wires. Joining k distinct boundary wires requires at least k−1 gates by connectivity. Equal supports may be reused.

For each candidate support a, the certificate charges a nonnegative integer price for each possible shared child b. The cheapest cover of a by available children at these prices is computed exactly by a subset recurrence. Subtracting all prices charged for the possible use of a from the cost of selecting a gives a lower bound. Every use charge in a realized network is offset by the corresponding selected-child deduction. Each requested output contributes its lower bound, while an optional support contributes the minimum of zero and its lower bound. The sum, divided by the price scale and rounded up, gives the integer gate bound. Run `python check_costs.py`. The same script checks a separate positive-rectangle weight certificate.

The Lean files use the pinned Lean 4.36.0, project commit 624acb3fb2189a78719c262c1af407bd73fb3b5c, and its PromiseColTree evaluator.

## Shard 63 circuits

OneNot.lean gives an exact 181-gate circuit. OneNotPartial.lean uses 170 gates, misses 13 positive cells and accepts no negative cell. Both use a single NOT gate. For each circuit Lean checks fan-in, size, the qualifying inverter mask, the represented matrix, and the error counts. FinalAudit.lean prints the axioms for those declarations and the 15-product construction.

## Raw leaves without sharing

Any unshared binary formula in the same OR-of-products form needs at least 219 raw leaves, hence at least 218 gates. For any all-positive rectangle on row set U and column set V, the integer weights in `leafweights.json` sum to at most 100,000 times (|U|+|V|). Their total on the positive graph is 21,812,113. Every product covers at most two rectangles, and the sum of their row and column counts is at most the number of raw leaves in its two operands. Summing the rectangle inequalities therefore gives the bound even if products overlap. Run `python check_leaves.py` to verify it with integer arithmetic.

For the displayed 170-gate circuit, 13 errors is the minimum after replacing any one gate while retaining the output. This also holds if the replacement changes the shard. An independent bit-column enumeration tests 4,209,115 replacements, including constants, all NOT inputs, and all unordered AND/OR inputs with repetition. Single-input identities and out-of-range reads introduce no additional truth tables. Changing only the output wire also gives at least 13 errors. Run `python check_replacements.py`.
