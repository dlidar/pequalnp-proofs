#!/usr/bin/env bash
set -euo pipefail
# Invoke from any directory in the checked-out repository, with the pinned
# Lean toolchain installed and Mathlib's build cache populated.
source_dir=$(cd "$(dirname "$0")" && pwd)
repository=$(git -C "$source_dir" rev-parse --show-toplevel)
cd "$repository/lean"
lake build PEqualNP.Defs
proof_build=$(mktemp -d)
trap 'rm -rf "$proof_build"' EXIT
project_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$proof_build:$project_path"
# The current directory selects the project's lean-toolchain file.
for module in Core Logic Upper Branch{0..32} Join; do
    lean -R "$source_dir" -o "$proof_build/$module.olean" "$source_dir/$module.lean"
done
python3 "$source_dir/search_bound.py"
