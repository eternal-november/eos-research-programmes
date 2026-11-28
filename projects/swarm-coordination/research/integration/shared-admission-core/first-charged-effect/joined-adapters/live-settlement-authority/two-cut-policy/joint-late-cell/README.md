# Joint late-cut obstruction and a paid occupancy observation
Run `set -o pipefail; python3 -B joint_cut.py --source path --warehouse path --support path | cmp - JOINT_CUT_EXPECTED.txt`.
In the archived bundle the flags can be omitted; it carries the same
source and parent helpers as the verified two-cut fixture. In the repo
the relative parent replay helper is discovered automatically, and the
flags point at the pinned source, warehouse and support materializations.
The archive's SHA256SUMS records the exact inputs. Lean/Mathlib checks the
structural results independently of the extracted replay.
