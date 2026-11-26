# Produce a qualified recovery graph delta incrementally

The frozen named-cell producer feeds actual semantic row changes to
the pinned finite checker. Active-read re-evaluation differs from
syntactic invalidation; changes in support are recorded even when
that row's output stays equal. The explicit trace oracle, strong
syntactic comparator, and counterexample agree in their stated
roles. Nothing here infers an unobserved resource alias.

Materialize SOURCE.tsv from the integration/incremental-reuse folder
of commit 298aa75260b01d5f1512a2c4c291a6dc29ea4c3d as upstream files.
Python standard library:

    python3 -B probe.py | cmp probe.json -
    python3 -B compose.py /path/to/upstream | cmp results.json -

ReadTrace.lean checks the conditional read-stability lemma in Lean 4.35
with Mathlib. Patch_Producer.tex describes cost accounting and scope.
