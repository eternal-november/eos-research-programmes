# Exact Boolean deadline profile under an admissible outage cap

Civilian simulation. Reuses the scoped membership fixture to test
which ready histories remain indistinguishable under a changed
partner outage cap. It does not assume those histories are observable
in advance, or certify a bound supplied by an actual device.

    bash replay.sh up | cmp - EXPECTED.txt

Lean 4.28.0 with Mathlib checks the comparison and amendment lemmas.
The Space archive includes the entire pinned source input tree.
