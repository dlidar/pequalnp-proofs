#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_PATH="$PWD:${LEAN_PATH:-}"
for name in Upper Near FactorCriterion SplitCore Cert{0..7} Classification UpperCore Pos{0..9} Full Types Match; do
  lean -o "$name.olean" "$name.lean"
done
python3 bound.py
cat certified
