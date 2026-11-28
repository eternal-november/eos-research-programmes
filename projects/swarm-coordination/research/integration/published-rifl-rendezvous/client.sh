#!/usr/bin/env bash
set -euo pipefail
base=$(cd "$(dirname "$0")" && pwd)
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
while read -r file blob; do
    test "$(git hash-object "$base/source/$file")" = "$blob"
done < "$base/SOURCE.tsv"
cp "$base/source/RpcTracker.h" "$base/client.cc" "$t"
sed '/^#include "/d' "$base/source/RpcTracker.cc" > "$t/tracker.inc"
c++ -std=c++17 -O2 -Wall -Wextra -Werror "$t/client.cc" -o "$t/check"
"$t/check"
