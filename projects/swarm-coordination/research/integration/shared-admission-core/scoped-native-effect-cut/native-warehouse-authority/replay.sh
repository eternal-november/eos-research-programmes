#!/bin/sh
set -eu
H=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
cd "$H"
export OPENBLAS_NUM_THREADS=1
while IFS="$(printf '\t')" read -r dest repo rev path sha; do
    test "$(git hash-object "source/$dest")" = "$sha"
done < SOURCE.tsv
while IFS="$(printf '\t')" read -r dest repo rev path sha; do
    test "$(git hash-object "radio_up/$dest")" = "$sha"
done < RADIO_SOURCE.tsv
while IFS="$(printf '\t')" read -r dest repo rev path sha; do
    test "$(git hash-object "$dest")" = "$sha"
done < KERNEL_SOURCE.tsv
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
cp -a source "$D/"
cp revise.py paired.py cut_contract.h gate_cut.cpp "$D/"
cd "$D"
cp source/journal_effect.cc source/replay_effect_cut.py source/first_effect.hpp source/support.py .
python3 -B revise.py
python3 -B paired.py
g++ -std=c++17 -O2 gate_cut.cpp -o "$D/cut_check"
python3 -B journal_effect.py --source "$H/radio_up" --warehouse source/warehouse --support support.py --cut "$D/cut_check"
