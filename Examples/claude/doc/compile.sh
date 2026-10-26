#!/bin/sh
# Build comparison.pdf from comparison.tex.
#   ./compile.sh          build the PDF
#   ./compile.sh clean    remove the build files (keeps the PDF)
set -e
cd "$(dirname "$0")"

if [ "$1" = clean ]; then
  latexmk -c comparison.tex
  exit 0
fi

if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error comparison.tex
else
  # without latexmk: run twice so references resolve
  pdflatex -interaction=nonstopmode -halt-on-error comparison.tex
  pdflatex -interaction=nonstopmode -halt-on-error comparison.tex
fi
