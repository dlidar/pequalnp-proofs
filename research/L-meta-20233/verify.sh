#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_PATH="$PWD:${LEAN_PATH:-}"
for unit in Upper Near Quotient24 EditNear NineWire24 EightWire24 ForcedOr Match FactorCriterion SplitCore Cert{0..7} Classification UpperCore Pos{0..9} Full Types Isolation; do
  lean -o "$unit.olean" "$unit.lean"
done
python3 audit.py
