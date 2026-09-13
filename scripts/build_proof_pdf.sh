#!/usr/bin/env bash
# Compile a paper source at the repo root into its PDF. Usage: scripts/build_proof_pdf.sh [basename]
# Default basename: separated_intervals_reciprocal_sum_one (the current paper); the earlier manuscript is
# erdos_289_land_2026-09-04. Requires pdflatex + latexmk (texlive-latex-extra, texlive-fonts-recommended, latexmk).
set -euo pipefail
repo="$(cd "$(dirname "$0")/.." && pwd)"
base="${1:-separated_intervals_reciprocal_sum_one}"
src="$repo/$base.tex"
out="$repo/$base.pdf"
build="${TMPDIR:-/tmp}/erdos289-pdf-build-$base"
mkdir -p "$build"
cp "$src" "$build/"
( cd "$build" && latexmk -pdf -interaction=nonstopmode -halt-on-error "$base.tex" >"$build/latexmk.log" 2>&1 ) \
  || { echo "latexmk failed; see $build/latexmk.log"; tail -40 "$build/latexmk.log"; exit 1; }
cp "$build/$base.pdf" "$out"
echo "wrote $out ($(pdfinfo "$out" | awk '/^Pages/ {print $2}') pages)"
