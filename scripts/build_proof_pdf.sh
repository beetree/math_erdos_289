#!/usr/bin/env bash
# Compile erdos_289_full_proof.tex into erdos_289_full_proof.pdf at the repo root.
# Requires pdflatex + latexmk (texlive-latex-extra, texlive-fonts-recommended, latexmk).
set -euo pipefail
repo="$(cd "$(dirname "$0")/.." && pwd)"
src="$repo/erdos_289_full_proof.tex"
out="$repo/erdos_289_full_proof.pdf"
build="${TMPDIR:-/tmp}/erdos289-pdf-build"
mkdir -p "$build"
cp "$src" "$build/"
( cd "$build" && latexmk -pdf -interaction=nonstopmode -halt-on-error "$(basename "$src")" >"$build/latexmk.log" 2>&1 ) \
  || { echo "latexmk failed; see $build/latexmk.log and $build/${src##*/}"; tail -40 "$build/latexmk.log"; exit 1; }
cp "$build/erdos_289_full_proof.pdf" "$out"
echo "wrote $out ($(pdfinfo "$out" | awk '/^Pages/ {print $2}') pages)"
