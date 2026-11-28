# Blind coupled wheel stopping under a stipulated saturation response

The full archive contains the four pinned Gazebo source files. For Git reproduction, native_replay.py lists exact hashes, revisions and paths. Dependencies: Python 3 and g++ C++17.

```sh
set -e -o pipefail
python3 -B derive.py | cmp - EXPECTED.json
python3 -B derive.py --rows | cmp - ROWS.txt
python3 -B native_replay.py < ROWS.txt | cmp - NATIVE.txt
```

ROWS.txt lists saturation mask (1 left, 2 right), fault state, five pairs of desired wheel speeds and two expected scaled wheel distances. The source writes desired targets, not the saturated responses. The latter are a different explicitly modeled plant law. SaturationScope.lean checks the arithmetic.
