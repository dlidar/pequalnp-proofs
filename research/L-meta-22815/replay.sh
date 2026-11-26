#!/usr/bin/env bash
set -euo pipefail
# Run inside this directory in a checkout with both earlier research commits.
git show 98c67ee132d71cfdd16ce648747264ba73a4dc76:research/L-meta-20973/Lower.lean > template-Lower.lean
git show 98c67ee132d71cfdd16ce648747264ba73a4dc76:research/L-meta-20973/Upper.lean > template-Upper.lean
for file in Lower.lean Upper.lean find.py; do
    git show "6a9513df2aacbdacb36d562ec1584dcd4659af35:research/L-meta-19264/$file" > "not-$file"
done
