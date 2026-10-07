#!/bin/sh
# Build the PDF and an arXiv upload bundle (arXiv does not run BibTeX, so the .bbl is included).
set -e
cd "$(dirname "$0")"
name=distance-set-similarity-schilly-2026
latexmk -pdf -interaction=nonstopmode -halt-on-error "$name.tex"
rm -rf arxiv && mkdir arxiv
cp "$name.tex" "$name.bbl" arxiv/
tar -C arxiv -czf "$name-arxiv.tar.gz" "$name.tex" "$name.bbl"
echo "bundle: $(pwd)/$name-arxiv.tar.gz"
tar -tzf "$name-arxiv.tar.gz"
