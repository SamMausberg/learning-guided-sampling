#!/bin/sh
# Build learning-guided-sampling.pdf in a temporary directory and copy it back.
# Requires pdfLaTeX with the packages listed in the preamble.
set -e
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp "$here"/*.tex "$tmp/"
cd "$tmp"
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-1791936000}"
export FORCE_SOURCE_DATE=1
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error learning-guided-sampling.tex > "$here/build.log" 2>&1
done
if grep -q "Rerun to get" learning-guided-sampling.log; then
  echo "cross-references did not settle" >&2
  exit 1
fi
cp learning-guided-sampling.pdf "$here/"
echo "built $here/learning-guided-sampling.pdf"
