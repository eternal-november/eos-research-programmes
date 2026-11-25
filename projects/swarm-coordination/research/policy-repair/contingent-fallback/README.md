# Contingent fallback while a source and its prior effect are both live

[Statement and proofs](Contingent_Fallback_And_Scoped_Discovery.tex).

```sh
python3 -B live.py | cmp replay.txt
python3 -B service_run.py | cmp service.txt
python3 -B footprint.py | cmp footprint.txt
python3 -B scoped.py | cmp scoped.txt
python3 -B integrated.py | cmp integrated.txt
```

Lean 4.35.0 with Mathlib checks four interface, counting and time lemmas
in `ContingentSlack.lean`. The alternating-matching argument and
physical-source scope are in the technical note. This is a deterministic
civil simulation, not a trust mechanism for real hardware or an
independently selected transfer.
