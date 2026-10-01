#!/usr/bin/env bash
# Build into the ignored .build directory; update the tracked PDF explicitly.
set -euo pipefail
update_pdf=false
case "${1:-}" in
  '') ;;
  --update-pdf) update_pdf=true ;;
  --help|-h)
    printf 'Usage: %s [--update-pdf]\nBuild .build/main.pdf; --update-pdf also replaces main.pdf.\n' "$0"
    exit 0 ;;
  *) printf 'Unknown option: %s\n' "$1" >&2; exit 2 ;;
esac
if (( $# > 1 )); then
  printf 'Usage: %s [--update-pdf]\n' "$0" >&2
  exit 2
fi
paper_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$paper_dir"
for dependency in latexmk pdflatex bibtex kpsewhich grep; do
  command -v "$dependency" >/dev/null || { echo "Missing dependency: $dependency" >&2; exit 1; }
done
for package in amsart.cls mathpazo.sty microtype.sty mathtools.sty booktabs.sty geometry.sty hyperref.sty xurl.sty; do
  kpsewhich "$package" >/dev/null || { echo "Missing TeX package: $package" >&2; exit 1; }
done
build_dir=.build
mkdir -p "$build_dir"
export SOURCE_DATE_EPOCH=1790812800
export FORCE_SOURCE_DATE=1
export TZ=UTC
export LC_ALL=C
latexmk -pdf -pdflatex='pdflatex %O "\pdftrailerid{}\input{%S}"' \
  -outdir="$build_dir" -interaction=nonstopmode -halt-on-error -file-line-error main.tex
if grep -n -E 'LaTeX Warning: (Reference|Citation).*undefined|There were undefined references|multiply defined' "$build_dir/main.log"; then
  echo 'Unresolved or duplicate references' >&2
  exit 1
fi
if "$update_pdf"; then
  cp "$build_dir/main.pdf" main.pdf
  printf 'PASS: paper built and tracked PDF updated (main.pdf)\n'
else
  printf 'PASS: paper built (.build/main.pdf)\n'
fi
