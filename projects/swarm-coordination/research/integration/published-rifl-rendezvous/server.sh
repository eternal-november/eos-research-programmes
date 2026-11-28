#!/usr/bin/env bash
set -euo pipefail
base=$(cd "$(dirname "$0")" && pwd)
while read -r file blob; do
    test "$(git hash-object "$base/source/$file")" = "$blob"
done < "$base/SOURCE.tsv"
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
cp "$base"/{server.cc,extract_server.py} "$t"
ln -s "$base/source" "$t/source"
cd "$t"
python3 -B extract_server.py
c++ -std=c++17 -Wall -Wextra -Werror -O2 server.cc -o check
./check
