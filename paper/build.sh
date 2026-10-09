#!/usr/bin/env bash
# Build a local PDF; preserve the published arXiv PDF in main.pdf.
set -euo pipefail
case "${1:-}" in
  '') ;;
  --help|-h)
    printf 'Usage: %s\nBuild .build/main.pdf with pdflatex; main.pdf remains the published arXiv PDF.\n' "$0"
    exit 0 ;;
  *) printf 'Unknown option: %s\n' "$1" >&2; exit 2 ;;
esac
if (( $# > 1 )); then
  printf 'Usage: %s\n' "$0" >&2
  exit 2
fi
paper_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$paper_dir"
for dependency in latexmk pdflatex bibtex kpsewhich grep; do
  command -v "$dependency" >/dev/null || { echo "Missing dependency: $dependency" >&2; exit 1; }
done
for package in article.cls geometry.sty amsthm.sty natbib.sty tikz.sty tcolorbox.sty tabularray.sty cleveref.sty; do
  kpsewhich "$package" >/dev/null || { echo "Missing TeX package: $package" >&2; exit 1; }
done
mkdir -p .build
# arXiv v1 prints October 8, 2026. Pin the clock used by the source's date macro.
export SOURCE_DATE_EPOCH=1791417600
export FORCE_SOURCE_DATE=1
export TZ=UTC
export LC_ALL=C
latexmk -g -pdf -pdflatex='pdflatex %O "\pdftrailerid{}\input{%S}"' \
  -outdir=.build -interaction=nonstopmode -halt-on-error -file-line-error main.tex
if grep -n -E 'LaTeX Warning: (Reference|Citation).*undefined|There were undefined references|multiply defined' .build/main.log; then
  echo 'Unresolved or duplicate references' >&2
  exit 1
fi
printf 'PASS: paper built (.build/main.pdf)\n'
