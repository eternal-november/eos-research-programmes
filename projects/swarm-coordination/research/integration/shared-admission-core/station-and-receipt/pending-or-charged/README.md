# Pending versus charged at a supplier change

Changing the designated supplier can make a previously irrelevant sender's outstanding charge matter to a live report. No receive callback can mean either a pending, removable probe or an erased but already charged one. The mounted broker state distinguishes them. A preauthorized fallback covers the latter if the original charge still makes the new primary too expensive.

- [Statement, exact cut and limits](Queue_Effect.tex)
- `Cut.lean`: arithmetic boundary and shared-observation obstruction, Lean 4.35.0 with Mathlib.
- `SOURCE.tsv`: pinned inputs (relative input path, repository, ref, source path, Git blob).
- Reproduce: put the pinned inputs under INPUT, then run `sh replay.sh INPUT > actual.json` and `cmp expected.json actual.json`. Requires Python 3, a C++17 compiler and Git. The replay uses extracted selected source and native callbacks, not a running ROS/Gazebo mission.

Supplier authority, optional cancellation and fallback admissibility are authored. The native all-member pose gate remains. No scheduler superiority, field guarantee, independent mission acceptance or obligation closure.
