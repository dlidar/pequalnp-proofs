#!/usr/bin/env bash
# Run inside the research directory with the pinned checkout's lake environment.
# LEAN_PATH must contain its built PEqualNP definitions, including Represents.
set -eu
root=$(pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
mkdir -p "$build/PEqualNP/Research"
# Lean selects one search root per top-level package. Overlay the two extra
# research modules onto all compiled project imports without editing the project.
python3 - "$build" <<'PY'
import os
import sys
from pathlib import Path
out = Path(sys.argv[1]) / 'PEqualNP'
for prefix in os.environ['LEAN_PATH'].split(os.pathsep):
    package = Path(prefix).resolve() / 'PEqualNP'
    if not package.is_dir():
        continue
    for source in package.rglob('*.olean'):
        dest = out / source.relative_to(package)
        if dest.exists() or dest.name in {'L_meta_3865_restriction.olean', 'L_meta_2071_flag_pinning.olean'}:
            continue
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.symlink_to(source)
PY
export LEAN_PATH="$build:$LEAN_PATH"
for f in L_meta_3865_restriction L_meta_2071_flag_pinning; do
  lean -R "$root/deps" -o "$build/PEqualNP/Research/$f.olean" "$root/deps/PEqualNP/Research/$f.lean"
done
for f in Support Family CloneUpper Restrict ClonePin CloneLift CloneCosts; do
  lean -R "$root" -o "$build/$f.olean" "$root/$f.lean"
done
lean -R "$root/unrestricted" -o "$build/Lower.olean" "$root/unrestricted/Lower.lean"
lean -R "$root" -o "$build/CloneExact.olean" "$root/CloneExact.lean"
