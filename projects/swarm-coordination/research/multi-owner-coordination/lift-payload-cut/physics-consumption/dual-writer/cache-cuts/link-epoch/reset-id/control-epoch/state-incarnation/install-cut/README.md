# Scope and replay

This extends [the pinned allocation revival replay](https://github.com/eternal-november/eos-research-programmes/pull/761) and discharges a development-side premise of [the recurring writer fixture](https://github.com/eternal-november/eos-research-programmes/pull/830), not deployment integration.

The three source files in INPUTS.tsv are from Gazebo Sim 9 commit `62f198e0478159549b748c4b4c66f0cbe2fcbf6f`. Fetch each named source path without altering newlines. For a clean artifact checkout with source pins staged in `pins`, run `set -o pipefail; python3 -B replay.py pins | cmp - EXPECTED.txt`. In the complete evidence ZIP the pin directory is `.`. The output columns are arm, exact matched verdict count, qualified affected completions, unauthorized modeled writes, and unaffected opportunities. Arms 0–4: last received, maximum received, writer epoch, scoped install, global freeze. Check Install_Cut.lean with AXLE Lean 4.36.0 and Mathlib.

The simulator supplies the actual graph and transient birth event. The adapter and writes being authorized are modeled. Refer to Install_Cut.tex for assumptions not supplied by the source.
