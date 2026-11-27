#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd)
project_lean=$(cd "${1:?provide the lean directory of the pinned project checkout}" && pwd)
export PATH="$(cd "$project_lean" && lake env lean --print-prefix)/bin:$PATH"
export LEAN_PATH="$source_dir:$(cd "$project_lean" && lake env printenv LEAN_PATH)"
cd "$source_dir"
lean --version
for module in Mass Decode Grid Code Uniform Sample Short Sharp Hash Project Transport LocalFit Combine Design; do
  lean -o "$module.olean" "$module.lean"
done
lean Audit.lean
