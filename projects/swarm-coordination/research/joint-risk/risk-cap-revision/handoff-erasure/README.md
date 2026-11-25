# Risk after a handoff with an erased record

[Model, sharp bound and scope](Risk_After_Handoff.tex). The replay distinguishes completed work from admissions and preserves exposure from the old role. Both correlation laws are authored and no field risk rate is inferred.

```sh
python3 -B replay.py | cmp REPLAY.txt -
lean RiskHandoff.lean
```

Lean 4.35.0 with Mathlib checked the rational lemmas. See [AXIOMS.json](AXIOMS.json).
