#!/bin/sh
set -eu
cd "$(dirname "$0")"
test "$(git hash-object receiver.py)" = be62ee669c6194af7c75f35107ae58736b36a547
python3 -B extract.py
bin=$(mktemp)
trap 'rm -f "$bin"' EXIT
"${CXX:-g++}" -std=c++17 -Wall -Wextra -Werror fixture.cpp -o "$bin"
"$bin"
python3 -B fence.py
