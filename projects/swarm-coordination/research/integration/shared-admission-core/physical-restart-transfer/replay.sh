#!/bin/sh
set -eu
s=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
for f in "$1/native_source.py:9797bf36970d5eb14fef7a150fab7562c450dff6" \
         "$1/rware_rotation.py:9803d1607cccf88a4a58e58f18528232790056be" \
         "$1/isolated.py:610a81b316a9b3538106387467c4e2f4437b28f4" \
         "$2/native.py:3c8870664b7bd6054cd756a6ffc7c365d8aae0c6" \
         "$2/guard.py:189ed7db9a796f9f083610d9fb3e7ef93c5b1080" \
         "$3/native.py:dcba6da00966bb61d72134662947d429ea1a6c35" \
         "$3/release.py:2b3da4f85d129bf1c31cd9d3594c537d5ec5c654" \
         "$4/core.py:687bf1250c6725992b6de696d0781d7948b4a89e"
do test "$(git hash-object "${f%:*}")" = "${f##*:}"; done
python3 -B "$s/replay.py" "$@"
