#!/usr/bin/env bash
set -euo pipefail
# Run from a project Lean environment with Mathlib and PEqualNP.Defs.Represents built.
cd "$(dirname "$0")"
export LEAN_PATH="$PWD/split:$PWD:${LEAN_PATH:-}"
lean -o Upper.olean Upper.lean
lean -o Formulas.olean Formulas.lean
lean -o ReaderExamples.olean ReaderExamples.lean
python3 formula_profiles.py
python3 shared_profiles.py
python3 triple_reader.py
cd split
for m in Core Logic Branch{0..37} Lower; do
  lean -o "$m.olean" "$m.lean"
done
