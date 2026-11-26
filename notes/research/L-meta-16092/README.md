# L-meta-16092

The six-input target has truth-table integer `3937069192 * 2^32 + 3901227008`, with input zero as the least significant coordinate. The desk asks for at most nine gates, including a one-input inverter. Pinned Lean 4.36.0 checked the exact negation of the desk statement. The ordinary minimum is nine gates. Requiring a one-input NOT raises the minimum to ten. The ten-gate witness adds an unused inverter, which the statement permits. All three final results depend only on propext, Classical.choice, and Quot.sound.

The explicit nine-gate circuit in `Upper16092.lean` uses AND and OR exclusively.

The signed live-set search allows complements at zero cost and counts the remaining gates. Its completeness argument is adapted from binharold’s upstream PR #15616 and the six-input specialization in PR #20132. This calculation uses the 64 positive/negative pairs in `pairs.json`. All 52 Boolean-cube boundary edges are present. The generator writes 65 first-step certificates. Lean checks the list of children at each split and each remaining search by kernel reduction. The statements in `ExactNegation.lean` and `Optima.lean` combine these checks with the explicit circuits.

From a checkout containing this directory and the project's pinned Lean toolchain, run `bash check.sh` from this directory. The script uses a temporary directory for the generated Lean files and compiled modules.
