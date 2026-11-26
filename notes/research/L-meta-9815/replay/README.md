# Lean replay of the binary-gate classification

Pinned Lean 4.36.0 checked the exact minimum decoder size for every one of the 182 choices of AND or OR on distinct inputs. All 251 named theorems passed the audit for `propext`, `Classical.choice`, and `Quot.sound`. The integer verifier in the parent directory checks the certificates independently.

From a checkout of this branch, run `bash check.sh` in this directory. The generator recreates 94 certificate modules, and the script checks `Classification.lean` and audits the named declarations. The statement for all 182 choices is `exact_per_cache`. The minimum over all choices, allowing repeated operands, is `best_cache_size`.

`Prune.lean` also proves that any collection of auxiliary signals vanishing on every minimal positive input can be replaced simultaneously by false in an exact monotone decoder. This includes all conjunctions of three distinct raw inputs.
