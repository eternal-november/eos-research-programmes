# Fallible source probes with nonfree failed attempts

[Statement and proofs](Charged_Probes_And_Actionable_Evidence.tex).

```sh
python3 -B charged.py | cmp replay.txt
python3 -B overlap.py | cmp overlap.txt
python3 -B packing.py | cmp packing.txt
python3 -B coupled.py | cmp coupled.txt
python3 -B provenance.py | cmp provenance.txt
python3 -B downstream.py | cmp downstream.txt
```

Lean 4.35.0 with Mathlib checks four supporting interface and arithmetic
lemmas. The scripts distinguish physical acquisition, delivery and actual
cleanup, use the same modeled observations and resource charges for the
direct references, and include an exact small Hall witness certificate.
No independent mission, field measurement or advance over the matched
exact reference is claimed.
