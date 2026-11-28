#!/bin/bash
set -euo pipefail
base=$(cd "$(dirname "$0")" && pwd)
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
while IFS=$'\t' read -r name repo ref path sha;do
 test "$(git hash-object "$base/source/$name")" = "$sha"
done < "$base/SOURCE.tsv"
cp "$base"/source/* "$base/fixture.cc" "$base/extract.py" "$t"
cd "$t"
python3 -B extract.py
c++ -std=c++17 -O2 -Wall -Wextra -Werror -Wno-unused-parameter fixture.cc -o run
./run
