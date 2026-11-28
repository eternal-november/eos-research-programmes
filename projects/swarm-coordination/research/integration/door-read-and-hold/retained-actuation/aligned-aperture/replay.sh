#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
UP=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r dest repo rev original sha; do
    test "$(git hash-object "$UP/$dest")" = "$sha"
done < "$HERE/SOURCE.tsv"
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
python3 -B "$HERE/extract.py" "$UP/door.cpp" "$UP/DoorOpen.cpp" "$UP/SupervisorHasSession.cpp" "$UP/utils.hpp" > "$D/profiles"
PYTHONPATH="$UP" python3 -B "$HERE/compare.py" "$D/profiles"
