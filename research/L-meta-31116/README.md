# L-meta-31116 research

The graph has eight vertices and fourteen edges. The assignment asks for a strict saving from a single inverter when arbitrary sharing is allowed. This directory contains an explicit 14-gate monotone circuit, a general replacement theorem, and finite searches for smaller circuits.

## Universal inverter replacement

Let the inverter read a monotone signal h and let f be the desired monotone Boolean output. A replacement u works for every monotone downstream decoder precisely when u agrees with f wherever f and h differ. Necessity follows by choosing the decoder majority(f,h,z) for the distinguished wire z. It reproduces f when z is the complement of h. Monotonicity in z proves sufficiency. If a monotone replacement circuit reads h as an additional input, one may replace that input by any raw variable while retaining universal correctness.

The graph has fourteen minimal positive inputs and six maximal negative inputs, forming a twenty-element antichain. For monotone u it suffices to check a positive edge where h is false or a maximal independent set where h is true. Every trace is attainable, and deleting any of the twenty tests can change the answer. Universal.lean and Boundary.lean prove these assertions.

## Optimal unshared repairs

The accepting tests and rejecting tests of a separator form a rectangle. A top OR partitions the accepting tests, while a top AND partitions the rejecting tests. Conversely, any such partition combines two formulas of the indicated total leaf count. Leaves are input literals of positive polarity or constants. profiles.cpp evaluates this recurrence. verify-prices.cpp reads its output independently and checks the lower inequality at every partition and a tight construction at every state. The full table contains 1,048,576 prices.

Exactly 22 traces require 15 leaves, hence 14 binary gates. Among inverter inputs of minimum circuit size four, exactly two traces attain this price. They are the outputs of (x2 OR x3) AND (x1 OR x4 OR x7) and (x3 OR x6) AND (x1 OR x4 OR x7). No input attainable with three or fewer monotone gates forces more than 12 repair gates. prefixes.cpp includes DAGs with repeated use of any intermediate. Allowing the three earlier prefix signals for free reduces the replacement formula cost to 13 gates in each of the six extremal predecessor sets.

For an inverter immediately following those four prefix gates, Features.lean verifies that every monotone decoder for the graph still needs all eight raw bits, even with the five prefix outputs available for free. It gives a separate distinguishing row pair for every coordinate and prefix.

## Shared circuit searches

frontier.cpp keeps the signals that will be read again, including the designated output. A binary gate consumes two signals and adds their AND or OR. Either operand can be retained for later use. A circuit with k gates remaining can have at most k+1 live signals, by counting the change in live set size. Every minimal circuit induces such a traversal by marking each wire's final use. Constants, singleton gates and duplicate sample columns can be eliminated in a smallest nonconstant monotone separator. At each step every positive-negative row pair must still have a wire equal to one on the positive and zero on the negative.

fast.cpp independently tests legal wire retirements through the row pairs for which that wire is the sole separator. For AND the other operand must accept each such positive. For OR it must reject each such negative. When both operands separate the same pair, their AND and OR both preserve the separation. Merge.lean proves the pairwise equivalences for retiring one or both operands.

The C++ counts are computational results. The Lean audit covers the named Lean theorems. The general one-NOT comparison remains open.

## Inverter position

Alternation.lean proves a partial function on any preordered set has a monotone decoder with one complemented monotone feature exactly when there is no increasing chain labeled positive, negative, positive, negative in that order. The constructive direction uses the upward closure of the first negative in any positive-to-negative reversal. Late.lean shows an inverter entering only the final AND or OR can be bypassed for this target.

On the twenty extremal tests, the endpoint-based live-wire search excludes thirteen monotone gates with arbitrary fanout. The fourteen-gate construction is independently evaluated on the full cube and compiled in Lean. The live-wire search also excludes every circuit of size at most thirteen whose inverter reads a raw bit, or whose inverter input has one, two, three, four or five binary ancestors. The decoder after the inverter has arbitrary sharing. The three-, four- and five-gate cones have respectively 10,416, 188,832 and 3,908,352 normalized prefix signal sets. The scope is the transitive input cone of the inverter, regardless of its physical position in a straight-line program. A separate unrestricted SAT search returned UNKNOWN.

To replay an ancestor check, reorder the ancestors before the inverter and the remaining gates after it. Classify the live monotone prefixes in canonical topological order. Preserve all prefix outputs and append the complemented last output. The positive and negative rows are the extrema in each fiber of the inverter input. Any decoder on these features is monotone. If the negative wire is unnecessary, the entire circuit is equivalent to a shorter monotone circuit. Both the direct retirement check and the private-pair version have positive and negative controls, and are implemented separately.
