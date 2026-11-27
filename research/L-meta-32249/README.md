# L-meta-32249

This is fork research on the eight-input graph with edges in bounds.json. Reference.lean gives a 15-gate monotone construction and checks all 256 inputs in the pinned project. The unrestricted equality between monotone and one-NOT circuit sizes remains open.

## Formulas and shared gates

Sixteen leaves, or 15 binary gates, are necessary and sufficient for an unshared monotone formula. checkprofiles.cpp validates all 16,777,216 entries of the separating-formula recurrence. The same gate minimum holds for an unshared formula with one NOT available. If the inverted subtree has k leaves and the monotone context has d ordinary leaves, the total including the NOT is k+d. If k+d≤14 and k≥3, the context has at most eleven raw leaves. The previously checked three-coordinate interpolation theorem converts it into a monotone formula of at most thirteen leaves. For k=1 a monotone decoder with the complemented raw input needs at least 15 leaves. For k=2 it needs at least 14 with the complement of a raw AND or OR, including repeated operands by the raw-input bound. Its leaf count for the original context is d+1. checkweights.py verifies the 64 graph-specific integer matrices for these two cases.

Allowing one arbitrarily shared monotone internal signal still requires 15 gates. Fixing that signal to zero or one eliminates all its leaf occurrences from the decoder. The pinned generic lemma is CachePin.lean in the preceding L-meta-29313 directory. The ordinary separator costs bound both the prefix and its two fixed decoders. To fit at most 14 gates the prefix would need at most eight. one-share-check.cpp enumerates all prefix functions at minimum sizes through eight. It tests the surviving 343 candidates with a separate threshold recurrence, and none meets its budget.

## Monotone messages across vertex cuts

Cut.lean proves that an encoder admits a monotone decoder precisely when it is monotone and ordering two codes orders their residual functions (with monotonicity already known in the receiver's inputs). Opposing residual values require a separating bit. A bit cannot serve two conflicting pairs. cutwidth.py constructs encoders, while check-cuts.py directly checks their monotonicity and ordering against the full truth table. Lower bounds are witnessed by cliques or by 25 tiny coloring proofs, totaling 93 branch nodes. The width is determined for all 255 nonempty cuts.

For the 35 unordered balanced splits, the minimum total number of monotone bits sent by the two blocks is five in two splits, six in twelve, seven in eleven and eight in ten. gen-balanced.py produces individual Lean statements asserting necessary and sufficient widths for the 70 oriented balanced cuts. Each uses the exact original target. Generated research files can be rebuilt from the sources in this directory.
