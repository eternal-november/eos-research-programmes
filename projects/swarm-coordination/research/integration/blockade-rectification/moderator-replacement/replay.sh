#!/bin/sh
set -eu
# Usage: sh replay.sh parent_of_pinned_repositories eigen3_include
study=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$1" && pwd)
eigen=$2
tab=$(printf '\t')
while IFS="$tab" read -r repo rev blob file
do
  test "$(git hash-object "$root/$file")" = "$blob"
done < "$study/SOURCE.tsv"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
c++ -std=c++17 -O1 -I"$eigen" -I"$root/rmf_traffic/include" -I"$root/rmf_utils/include" \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/Constraint.cpp \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/Moderator.cpp \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/Participant.cpp \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/Rectifier.cpp \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/conflicts.cpp \
  "$root/rmf_traffic"/src/rmf_traffic/blockade/geometry.cpp "$study/replay.cc" -o "$dir/test"
"$dir/test"
