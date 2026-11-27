#!/bin/sh
set -eu
cd "$(dirname "$0")"
while IFS="$(printf '\t')" read -r name repo rev source sha; do
  test "$(git hash-object "$name")" = "$sha"
done < INPUTS.tsv
export OPENBLAS_NUM_THREADS=1
python3 -B committed_pose.py > observed_pose.json
cmp committed_pose.json observed_pose.json
python3 -B extract_radio.py
"${CXX:-g++}" -std=c++17 -O2 -Wno-return-type pose_deliver.cpp -o pose_deliver
python3 -B radio_at_cut.py > observed_radio.json
cmp radio_at_cut.json observed_radio.json
echo 'Matched 2,720 native suffix checks and 512 broker cases.'
