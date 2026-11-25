# Exact optical phase distance

[Statement, recurrence and witness](Exact_Phase_Distance.tex).
The unchanged parent alphabet gives a sharp phase threshold of
17 + 11e samples for e substitutions under the declared bit model.
For one substitution, identifying some entire word takes 32 samples
in the worst case. For two or more, phase may be known even while
no specific complete word has a uniquely determined payload.

Run from this folder:

    python3 -B phase_distance.py | cmp results.json -

The checker uses the exact parent alphabet and verifies its Git blob
ID. It checks the full minimum-cost vector shift, not only the lowest
entry. An independent block-distance check verifies the one-error
witness. No empirical camera or live fault timing claim is made.
