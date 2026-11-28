# Wheel slew and independently selected heading

Use the full archive, or materialize the four Gazebo pins named in native_replay.py and copy the exact derive.py from [#846](https://github.com/eternal-november/eos-research-programmes/pull/846) as prior_model.py (blob pin checked in solve.py). Dependencies are Python 3 and C++17.

```sh
set -e -o pipefail
python3 -B solve.py | cmp - EXPECTED.json
python3 -B solve.py --rows | cmp - ROWS.txt
python3 -B native_replay.py < ROWS.txt | cmp - NATIVE.txt
```

The modeled plant response is applied separately to native desired writes. Integer grid bounds for the correlated task and real-input analytic bounds for the heading-only interface are different claims. HeadingEvidence.lean checks arithmetic.
