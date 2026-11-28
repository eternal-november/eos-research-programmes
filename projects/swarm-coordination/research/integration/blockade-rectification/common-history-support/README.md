# Common-history support and bounded-deletion quotient

The standalone archive contains exact pinned sources and Eigen dependencies. From its root use:

```sh
set -e -o pipefail
out=$(mktemp)
sh study/replay.sh . eigen3 2>"$out" | cmp - study/NATIVE.txt
cmp "$out" study/QUERY-COUNTS.txt
rm "$out"
python3 -B study/event_support.py | cmp - study/RESULT.json
```

To reconstruct from Git, materialize the 21 exact source files in SOURCE.tsv at the indicated relative paths; provide a compatible Eigen 3 include directory; place this study's files under study. The same copy of C++ source is used in both forwarding arms. A reader sees a collapsed ready and assigned range, not an export of the internal queue. The Python constructor models a restricted exclusive crossing grammar, not Open-RMF's complete conflict solver.

Raw trace rows have two fields for forwarding arm and event word, then eight digits per cut: readiness and range end for each crossing contender, independent range end, incumbent reached, producer intent, forwarding at that cut. Last two digits are evaluator fields. No field independently certifies motion or clearance.
