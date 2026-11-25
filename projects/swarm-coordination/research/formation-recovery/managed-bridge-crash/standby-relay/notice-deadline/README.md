# Failed-member notice and one timed forwarding attempt

[Proof, interpretation and scope](Relay_Notice_Deadline.tex). Obtain [the pinned scenario file](https://github.com/KTH-DHSG/constrained_omrs/blob/cb87f91aaaa4e652de043704ce4dfb989e10bcde/src/constrained_omrs/scenario.py) as `scenario.py.upstream`.

```sh
set -o pipefail
python3 -B replay.py | cmp REPLAY.txt -
lean RelayNotice.lean
```

Python verifies the source blob ID, recorded geometry and independent finite acceleration comparison. The Lean check used 4.35.0 with Mathlib. No package versions or native simulation inputs are changed.
