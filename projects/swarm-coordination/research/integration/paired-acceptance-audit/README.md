# Preselection and paired-outcome audit

Development instrument only. No architecture, comparator, holdout or
acceptance threshold is selected here. No inventory disposition changes.

[Protocol, proof and current readiness](Paired_Acceptance_Audit.tex).
Replay with Python 3.10+:

    python3 -B replay.py | cmp expected.json -

18,252 synthetic profile comparisons with direct enumeration, nine rejected
transcript changes and four controls. Neither the commitment check nor the
exact bound certifies the provided evidence.
