# Braking a single-file chain

For initially nonincreasing speeds and common actuator limits, checking all pair spans is necessary and sufficient to preserve the adjacent gap bands and stop. The proof gives the exact minimum times to equalize and to stop. Adjacent braking checks alone are insufficient, and tied interior robots can need opposite control inputs even when their speeds are initially equal.

- [Theorem and continuous-time proof](Monotone_Chain_Braking.tex)
- [Lean arithmetic checks](TiedTangent.lean), Lean 4.35.0 and Mathlib
- [Exact rational replay](replay.py) and [recorded output](results.json)

Run `python3 replay.py | diff -u results.json -`. The theorem assumes a known initial state and common limits, with no new fault in the braking phase. It is not a distributed observation or hardware result.
