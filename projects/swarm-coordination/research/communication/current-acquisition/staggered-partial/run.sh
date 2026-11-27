#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
up=$(CDPATH= cd -- "$1" && pwd)
while IFS="$(printf '\t')" read -r local repo ref source blob; do
    test "$(git hash-object "$up/$local")" = "$blob"
done < "$here/SOURCE.tsv"
export PYTHONPATH="$up" OPENBLAS_NUM_THREADS=1
python3 -B "$here/seed.py" "$up/force_control.py"
python3 -B "$here/bias.py"
python3 -B "$here/verify_bias.py"
