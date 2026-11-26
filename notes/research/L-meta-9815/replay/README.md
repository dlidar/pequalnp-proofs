# Lean replay of the binary-cache certificates

The independent integer verifier in the parent directory has checked all 182 choices. These sources implement a separate Lean replay. The full build and axiom audit were in progress when this checkpoint was recorded. The parent directory's 37 theorems, including the ordinary and complemented-input results, have passed the permitted-axiom audit.

Run `bash check.sh` in this directory with the project's pinned toolchain. The generator recreates the 94 individual certificate modules from the packed integer data. The main conclusion is `exact_per_cache` in `Classification.lean`.
