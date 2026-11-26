#!/usr/bin/env bash
set -euo pipefail
proof_src=$(cd "$(dirname "$0")" && pwd)
repository=$(git -C "$proof_src" rev-parse --show-toplevel)
cd "$repository/lean"
lake build PEqualNP.Defs
proof_build=$(mktemp -d)
trap 'rm -rf "$proof_build"' EXIT
project_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$proof_build:$project_path"
for module in SupportGraph Overlap GridPacks Family OrbitData Assemble Case1 Orbit{0..15} Batch{0..21} Final AxiomOverlap FinalPlus; do
    lean -R "$proof_src" -o "$proof_build/$module.olean" "$proof_src/$module.lean"
done
