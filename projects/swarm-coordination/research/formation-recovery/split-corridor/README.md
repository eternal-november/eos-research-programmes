# Recovery across a radio break

[Statement, proof, and scope](Split_Formation_Recovery.tex). Each half can choose its own approach without exchanging positions when the stopped body is known. When only one half knows the stop, the example has a sharp deadline for establishing usable contact evidence.

- `python3 replay.py | cmp replay.txt`: exact split/global comparison on 60,720 integer configurations.
- `python3 active_boundary.py | cmp active_boundary.txt`: exact timed-contact policy comparison across 135 cases.
- `python3 ambiguity.py`: rational terminal witnesses in the two physical worlds.
- `lake env lean SplitFormation.lean` in Lean 4.35.0 with Mathlib. The replay checked the extremal join, matching known-world terminal witnesses, lack of a shared hidden-world action, and contact/deadline inequalities with no `sorryAx`.

Compare the [known-configuration physical oracle](../corridor-crash/README.md). These are source-scoped results: they assume local access and endpoint constraints, not a real radio or no-drift clock validation.
