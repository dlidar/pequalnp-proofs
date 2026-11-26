# Parity pivots in a PHP(4,3) refutation

L-pcx-120 asks whether a Res(⊕) refutation of the four-pigeon, three-hole formula can have at most 51 lines. These results give necessary conditions for such a refutation.

For each nonzero parity query, restrict the 4,096 assignments to each answer separately. An axiom cover of a halfspace is a set of input clauses such that every assignment in the halfspace falsifies at least one chosen clause. The smallest possible sum of the two minimum cover sizes is 31. It occurs exactly for the 12 single-variable pivots. For each such pivot the two halfspaces need 19 and 12 axioms.

For the proof in Lean, a packing consists of assignments whose sets of violated axioms are pairwise disjoint. Each assignment forces a separate axiom in the subderivation reached on its side of the pivot. SupportGraph.lean uses the dependency-graph lemmas from the merged upstream proof of L-pcx-118. GridPacks.lean connects the packing condition to the project's semantics. The 22 batch modules check packings for 86 representatives. The 16 orbit modules check that these cover all 4,095 nonzero pivots by permuting pigeons and holes. FinalPlus.lean states the resulting shared-line and shared-axiom bounds for the two parents of a semantically false line in a proposed short proof.

Run bash check.sh in this checkout with the pinned Lean environment to replay the formal proofs. Run cover.py, packing.py, and check_cover.py with Python 3 to reproduce the cover counts, packing witnesses, and independent check of all 172 halfspace optima.

trees.cpp minimizes the number of leaves of a tree that queries individual variables after a specified initial parity. Give it one decimal pivot mask per line. Zero requests a tree using only variable queries. Running verify_trees.py with arguments 0 9 4095 independently checks the three corresponding rows of trees.txt using sets of full assignments.

dictionary.py takes the upstream L_pcx_123.lean file as an argument and tests which lines of its 58-line refutation are indispensable in that dictionary, allowing arbitrary line order and semantic weakening. union_search.py additionally considers relabelings and restricts justifications to the indicated stage order. Set CADICAL to the pinned toolchain's solver. The generated CNFs count axioms and derived lines. lrat_check.py independently checks text LRAT certificates with RUP additions and rejects unsupported hints. These finite searches leave the unrestricted 51-line question open.
