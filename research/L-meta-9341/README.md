# Zero rectangles for L-meta-9341

The board is the complement of the 21 by 21 cyclic incidence matrix in the assignment. Row and column indices start at zero. A simultaneous shift by three has order seven. A simultaneous shift by seven has order three.

If seven slots in a cover are occupied by the seven translates of one legal nonempty rectangle under the shift by three, the residual needs at least nine more rectangles. Each original box may be enlarged to a maximal box by closing its column side and then its row side. Closure commutes with translation. The result allows all remaining rectangles to be chosen independently.

Run `python check_duals.py` and `python check_tight.py` with Python 3 and NumPy. The first verifier traverses every row subset of the original board, reconstructs all 25,235 maximal nonempty rectangles, checks the affine permutations, and verifies all integer dual weights. A cover by k rectangles can cover weight at most k times the largest individual rectangle weight. For two exceptional representatives this bound leaves eight slots to test. At each node the second verifier checks the chosen uncovered cell and visits every box that could cover it within the residual weight budget. Each trace has 2,673 branch points. The supplied JSON files are sufficient to replay these checks. To regenerate them run `python residual.py` (SciPy required) and `python tight.py`.

For invariant covers run `c++ -std=c++20 -O3 -mpopcnt orbit_search.cpp -o orbit_search`, `python quotrun.py`, and `python sym_near.py`. In a cover invariant under shift by seven, the minimum is 15. In a cover invariant under shift by three, it is 21. In the latter case maximal rectangle orbits have size seven and 21 single-row rectangles attain the bound. Thus every 13-rectangle solution must break each nonidentity cyclic symmetry. With shift-by-seven symmetry and at most 13 rectangles, at least six zeros are uncovered.

These finite searches establish restricted bounds. The unrestricted 13-rectangle question is open in this work.
