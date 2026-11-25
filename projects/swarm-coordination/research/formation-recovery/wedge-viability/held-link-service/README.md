# Held braking with a continuing link and a named terminal

[Proof and scope](Link_Preserving_Stopped_Service.tex). Continuously preserving an old range link and completing the new terminal exchange at rest can be tested in one held-command model. A permission report after the final command cut cannot repair disjoint admissible brake intervals.

Run `python3 -B replay.py | cmp replay.txt -`. The exact rational replay tests a direct whole-trajectory oracle. `LinkBrake.lean` checks three scoped lemmas in Lean 4.35.0 with Mathlib. A local actual-stop actuator event and a declared stationary delivery model are explicit premises, not events inferred from a robot result or field data.
