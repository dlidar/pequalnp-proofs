# L-meta-20340

The posted 8 by 8 matrix has 24 edges. Inputs are promised to contain exactly one row and one column. The assignment asks for a monotone circuit with at most 24 binary gates.

* Upper.lean gives a 28-gate circuit. Near.lean checks a 23-gate circuit that misses exactly three edges.
* For shared OR preprocessing on each side, AND gates forming rectangles, and a final OR, the exact minimum is 28 gates. There are 92 nonempty all-one rectangles. Each selected rectangle costs two tokens (one product and one final sum), with a one-token rebate for the output. A selected non-singleton row or column group costs one OR. Every group has at most three labels. A triple needs an activated pair among its three two-element subsets, and any such pair suffices. Thus the weighted Boolean model in bound.py represents this entire circuit class. A text LRAT refutation for the 27-gate bound was independently checked by check_rup.py. The checker verified 22,373 RUP additions. The two hashes identify the local CNF and certificate.
* Types.lean characterizes input subsets that admit a single monotone signal to a monotone decoder with access to all remaining raw inputs. Among all 65,536 subsets, the 58 possibilities are the empty and full sets, the 16 singletons, and the 40 pairs consisting of a nonincident row and column. The general four-row criterion is in FactorCriterion.lean.
* The unrestricted 24-gate existence claim is separate from these bounds. search.py encodes the full 64-row promise and checks its 28-gate control before searching.

Run verify.sh with the project's pinned Lean 4.36.0, Mathlib and PEqualNP.Defs.Represents in LEAN_PATH. The restricted SAT replay also needs Python, NumPy, SciPy and CaDiCaL on PATH.

At a budget of 24 gates, the sharp fewest missed positive cells in this rectangle model with no false positives is three. Near.lean checks an attaining 23-gate circuit. near_bound.py adds one coverage-slack variable per edge to the exact model and permits at most two misses. check_rup.py independently verified all 99,075 RUP additions ending in the empty clause. The hashes of the generated CNF and proof are in near-certificate-sha256.txt.
