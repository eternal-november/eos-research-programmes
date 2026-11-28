# Projected frame at the setter cut

Run `set -o pipefail; python3 -B replay.py pins | cmp - EXPECTED.txt`, using the nine files in INPUTS.tsv at the listed pins. Use AXLE 4.36.0 with Mathlib to check Projected_Frame.lean. The complete archive includes pins. The two adapters from [#832](https://github.com/eternal-november/eos-research-programmes/pull/832) keep their upstream revalidation, while the rotation stand-in adds signed pitch and world yaw.

Rows report arm, setter calls, correct calls, wrong calls, and missed feasible unchanged targets. Arms 0–4 are generation only, full orientation sameness, projected frame, direct output comparison, and effect-time recomputation with supplemental authority. Joined source calls are not hardware, dynamics or stock middleware validation.
