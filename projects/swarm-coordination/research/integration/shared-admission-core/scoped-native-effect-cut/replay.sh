#!/bin/sh
set -eu
H=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
U=$(CDPATH= cd -- "$1" && pwd)
P=$(CDPATH= cd -- "$2" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
cd "$H"
while IFS="$(printf '\t')" read -r dest repo rev path sha; do
    test "$(git hash-object "$dest")" = "$sha"
done < CUT_INPUTS.tsv
g++ -std=c++17 -O2 -Wall -Wextra -Werror residual_check.cpp -o "$D/residual_check"
"$D/residual_check"
g++ -std=c++17 -O2 -Wall -Wextra -Werror gate_cut.cpp -o "$D/gate_cut"
python3 -B compare_prior.py "$D/gate_cut"
SCOPED_CUT_BIN="$D/gate_cut" bash gate/replay.sh "$U" "$P" > "$D/gate.out"
cmp "$D/gate.out" gate/EXPECTED.jsonl
bash radio/replay.sh "$H/radio/up" > "$D/radio.out"
cmp "$D/radio.out" radio/EXPECTED.txt
cat "$D/gate.out" "$D/radio.out"
