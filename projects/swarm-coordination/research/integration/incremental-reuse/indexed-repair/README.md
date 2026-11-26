# Indexed receiver repair

Keeps adjacency, reverse incidence and rooted child links in one sequential
version owner. Validates exact verdicts against the prior worklist and full
reconstruction. The composed producer-to-verdict work and an optional
nondeterministic timing probe are separate outputs.

Put exact SOURCE.tsv inputs in an upstream folder. The first four files
are from integration/incremental-reuse at commit
298aa75260b01d5f1512a2c4c291a6dc29ea4c3d; dependency.py is from that
study's patch-producer subfolder at commit
51ded18db921fc439636b63c35052fdbd5be952f. Then run:

    python3 -B test.py /path/to/upstream | cmp results.json -
    python3 -B timing.py /path/to/upstream

SparseSeeds.lean checks the entrance lemma with Lean 4.35 + Mathlib.
The deterministic assertions do not measure timing. Observed-timing.json
is a captured local trial; numbers are not expected to repeat bytewise.
