# Four-row incidence cores for L-meta-17162

A four-row bipartite graph with minimum degree two on both sides and no four-cycle has distinct column neighborhoods. Encoding the four rows by bits gives fourteen labeled families, in four classes up to row and column permutations. The circuit output is the OR of the ANDs on the edges. Both sides have independent Boolean inputs.

| Column masks | Edges | Minimum vertex cover | Minimum binary gates with up to two preprocessing gates and a formula decoder |
|---|---:|---:|---:|
| 3, 5, 10, 12 | 8 | 4 | 11 |
| 3, 5, 6, 9, 10 | 10 | 4 | 13 |
| 3, 5, 6, 9, 10, 12 | 12 | 4 | 15 |
| 3, 5, 9, 14 | 9 | 4 | 12 |

The four left vertices cover the graph. An explicit matching of size four is printed for each graph by the independent verifier. An ordinary unshared formula attains every upper bound by ORing the four point stars.

## Lean results

Use the upstream pinned Lean 4.36.0 with Mathlib available. Run `bash verify.sh` from this directory with `lake` on the path and pass the upstream `lean/` project directory as the first argument. CoreClass, Census and Orbits prove the classification for arbitrary column count. Core0 through Core3 prove the exact number of leaves in an ordinary monotone formula for the four representatives. The generic signed rectangle argument in FormulaMass comes from the L-meta-18330 research branch. Audit prints the axiom dependencies.

## Integer certificates for shared preprocessing

Run `python3 verify.py` from any directory. The verifier uses the Python standard library. It independently reconstructs the graphs, automorphisms, maximal negative inputs and programs. It checks the four explicit circuits on all assignments. To regenerate the signed matrices, run `python3 weights.py` and then `python3 two.py` with NumPy and SciPy installed.

Each preprocessing gate may be AND or OR. Its inputs can be any two distinct raw inputs or earlier signals. The formula following the prefix may use all raw inputs and both cached signals any number of times. A gate with repeated operands can be bypassed. The cost counts every preprocessing gate and binary formula operation.

For each minimally positive input and maximal negative input, the certificate assigns an integer weight to the pair. At an AND node, partition the negative inputs between the two children. At an OR node, partition the positive inputs. Each leaf receives a rectangle consisting of positive rows where its signal is true and negative columns where it is false. If every such rectangle has weight at most C, a formula with d leaves has total weight at most Cd. To find the maximum leaf weight, the verifier enumerates every eligible row subset and sums the positive eligible column totals. This also works with negative weights. After accounting for zero, one or two cached gates, the certified lower bounds meet the four star constructions.

The programs cover 24,444 ordered two-gate preprocessors and 274 single gates across the four cores. The numerical two-gate bounds have an independent integer replay. The Lean lower-bound files cover ordinary formulas.

The unrestricted shared-circuit lower bound remains open. An unrestricted 14-slot SAT search on the six-column representative terminated by signal 9 without a verdict. The separate gate-elimination values in census.json are exploratory and play no part in the proofs above.
