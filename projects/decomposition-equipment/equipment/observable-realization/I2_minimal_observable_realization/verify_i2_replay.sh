#!/bin/sh
set -eu
cd "$(dirname "$0")"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
tar -cf "$work/source.tar" verify_i2.py verify_encoder_decoder.py finite_typed_realization.py encoder_decoder_draft.md realization_theorem_draft.md i2_minimal_realization_theorem.md baseline_comparison.md index_boundary_theorem.md verify_i2_results.json
mkdir "$work/extracted"
tar -xf "$work/source.tar" -C "$work/extracted"
(cd "$work/extracted" && python -m py_compile verify_i2.py verify_encoder_decoder.py finite_typed_realization.py && python verify_i2.py > replay.json && cmp verify_i2_results.json replay.json)
printf '%s\n' 'PASS: extracted source rerun byte-identical; py_compile PASS'
