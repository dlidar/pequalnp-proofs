# L-meta-32249

This is fork research on the eight-input graph with edges in bounds.json. Reference.lean gives a 15-gate monotone construction and checks all 256 inputs in the pinned project. The unrestricted equality between monotone and one-NOT circuit sizes remains open.

## Formulas and shared gates

Sixteen leaves, or 15 binary gates, are necessary and sufficient for an unshared monotone formula. checkprofiles.cpp validates all 16,777,216 entries of the separating-formula recurrence. The same gate minimum holds for an unshared formula with one NOT available. If the inverted subtree has k leaves and the monotone context has d ordinary leaves, the total including the NOT is k+d. If k+d≤14 and k≥3, the context has at most eleven raw leaves. The previously checked three-coordinate interpolation theorem converts it into a monotone formula of at most thirteen leaves. For k=1 a monotone decoder with the complemented raw input needs at least 15 leaves. For k=2 it needs at least 14 with the complement of a raw AND or OR, including repeated operands by the raw-input bound. Its leaf count for the original context is d+1. checkweights.py verifies the 64 graph-specific integer matrices for these two cases.

Allowing one arbitrarily shared monotone internal signal still requires 15 gates. Fixing that signal to zero or one eliminates all its leaf occurrences from the decoder. The pinned generic lemma is CachePin.lean in the preceding L-meta-29313 directory. The ordinary separator costs bound both the prefix and its two fixed decoders. To fit at most 14 gates the prefix would need at most eight. one-share-check.cpp enumerates all prefix functions at minimum sizes through eight. It tests the surviving 343 candidates with a separate threshold recurrence, and none meets its budget.

## Monotone messages across vertex cuts

Cut.lean proves that an encoder admits a monotone decoder precisely when it is monotone and ordering two codes orders their residual functions (with monotonicity already known in the receiver's inputs). Opposing residual values require a separating bit. A bit cannot serve two conflicting pairs. cutwidth.py constructs encoders, while check-cuts.py directly checks their monotonicity and ordering against the full truth table. Lower bounds are witnessed by cliques or by 25 tiny coloring proofs, totaling 93 branch nodes. The width is determined for all 255 nonempty cuts.

For the 35 unordered balanced splits, the minimum total number of monotone bits sent by the two blocks is five in two splits, six in twelve, seven in eleven and eight in ten. gen-balanced.py produces individual Lean statements asserting necessary and sufficient widths for the 70 oriented balanced cuts. Each uses the exact original target. Generated research files can be rebuilt from the sources in this directory.

## The two balanced five-signal partitions

For blocks {0,1,4,6} and {2,3,5,7}, the minimum total size of a monotone circuit with exactly five signals across the split is 15 gates. For {1,2,4,6} and {0,3,5,7}, the minimum is 16. The architecture consists of separate monotone block encoders and a joint monotone decoder. Each signal can be reused arbitrarily inside the decoder. The two displayed circuits were also evaluated on all 256 inputs.

Each two-signal encoder is unique up to output order. Exhaustive enumeration of all 166 nonconstant monotone functions on four inputs leaves 108 and 60 three-signal encoders in the respective splits. For the first split, 29 require a five-gate decoder and 79 require six. For the second, 35 need five and 25 need six. These are exact even with sharing. The decoder costs come from a five-input formula upper certificate and complete circuit enumeration through five gates. encoders.cpp counts the minimum joint gate costs of the signal families through seven gates, with a lower bound of eight for the rest. Those bounds suffice to prove the two optimum sums. The attained constructions are in balanced-83.json, balanced-86.json and Examples.lean.

The 15-gate lower bound also holds when any two preliminary monotone binary gates feed a monotone formula decoder. The second gate may read the first. Of 3,738 normalized programs, fixing both cache bits and accounting for their uses leaves 557 programs to test. The exact decoder threshold recurrence in two-cache.cpp excludes all 557 at the 14-gate budget. A circuit with fewer than two genuinely shared internal outputs was already covered by the arbitrary single-signal theorem.

Three monotone 14-gate circuits each have just one false positive. The respective input masks are 34, 130 and 72, obtained by adding edge 1–5, 1–7 or 3–6. All 256 inputs were checked for each construction. Changing up to two gates in these three concrete programs, using binary AND or OR on distinct earlier wires or a single unary NOT, did not produce the target.
