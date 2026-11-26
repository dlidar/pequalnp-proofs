# L-meta-4697 research

For a finite simple graph with an edge and no four-cycle, the optimum of the posted shared union pool is exactly the number of edges plus the minimum vertex-cover size, counting in the posted units. Subtract one to count gates. A minimum-size pool has exactly one product per member of a minimum cover and exactly one union per remaining edge. The proof turns the posted backwards-built list into indexed wires, orients every productive rectangle as a star, and charges the distinct leaves to shared union wires. Empty operands and repeated pool entries are allowed.

Application.lean proves an equivalence using the exact posted statement. What remains is the unrestricted AND/OR/NOT lower bound. Ordinary.lean derives the matching general upper bound from the project's EdgeUpper construction. These files are research on the problem.

Example.lean verifies a concrete cubic graph on 24 vertices with 36 edges, minimum cover 14 and normalized optimum 49 gates. Girth.lean certifies girth at least seven by edge-deletion distance potentials and specializes the assignment's implication. An exact 48-gate ordinary circuit on this graph would refute the assignment. The ordinary 49-gate upper bound is unconditional.

Use bash replay.sh in the fork checkout with its pinned Lean environment. LeafCount.lean reuses the leaf-count argument from dlidar's L-meta-4675 research. StarPools.lean reproduces the generic upper construction on the parent commit.

Run python3 edits.py for the 36 specified single-edge deletion circuits and all one-gate substitutions (AND, OR, NOT). It tests the 36 positive edge rows and 506 maximal independent negative rows. No single substitution passes even these rows. Run python3 truth.py for the independent exhaustive replay of all 16,777,216 inputs. The 49-gate circuit matches every row. Each 48-gate deletion misses 3,892, 3,899 or 3,951 inputs and has zero false positives. The computations cover these explicit templates. The unrestricted 48-gate question remains open.
