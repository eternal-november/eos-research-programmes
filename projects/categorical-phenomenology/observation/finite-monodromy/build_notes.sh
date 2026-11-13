#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")" && pwd)"
args=()
prefix=''
if [[ -n "${TEX_FALLBACK_FORMAT:-}" ]]; then
  args+=("-fmt=$TEX_FALLBACK_FORMAT")
  export TEXINPUTS="/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:."
  export TFMFONTS="/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//"
  export VFFONTS="/usr/share/texlive/texmf-dist/fonts/vf//:/usr/share/texmf/fonts/vf//"
  export T1FONTS="/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//"
  export ENCFONTS="/usr/share/texlive/texmf-dist/fonts/enc//:/usr/share/texmf/fonts/enc//"
  prefix='\pdfmapfile{+/usr/share/texmf/fonts/map/dvips/lm/lm.map}\pdfmapfile{+/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map}'
fi
for note in finite_cover_recovery evidence_limits; do
  dest="$root/rebuild/$note"
  mkdir -p "$dest"
  for pass in 1 2; do
    pdflatex "${args[@]}" -interaction=nonstopmode -halt-on-error -jobname="$note" -output-directory="$dest" "${prefix}\input{$root/$note/$note.tex}" > "$dest/build.log" 2>&1
  done
  printf 'Built %s\n' "$dest/$note.pdf"
done
