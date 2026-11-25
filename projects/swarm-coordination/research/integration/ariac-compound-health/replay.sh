#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
python3 -B "$ROOT/extract.py" "$1/task_manager_plugin.cpp" > "$D/upstream_extract.inc"
"${CXX:-g++}" -std=c++17 -O2 -I "$D" "$ROOT/native.cpp" -o "$D/native"
"$D/native" > "$D/rows"
cat "$D/rows"
python3 -B "$ROOT/switch_replay.py" "$1/robot_controller_switcher_node.py" "$D/rows"
python3 -B "$ROOT/ledger.py"
