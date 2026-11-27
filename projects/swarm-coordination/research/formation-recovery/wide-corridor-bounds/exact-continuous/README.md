# Exact continuous certificates for wider protected corridor intervals

[Completeness and certificate checks](Exact_Continuous_Corridor.tex).
For the earlier speed-only ordered corridor model, any feasible
continuous trajectory can be replaced by straight segments that visit
each relevant closed convex cell at most once. This includes feasible
paths whose cell membership changes infinitely often. Enumerating simple
cell routes and solving rational LPs therefore gives an exact
minimum, or a correct infeasibility verdict, on the declared model.

The replay audits 744 route solves using exact rational arithmetic,
checks 119 chords independently against the sensing invariant, and
matches the old same-information numerical planner. The motion is
not assumed coordinatewise monotone. The numerical proposal step in
this harness fails closed if it cannot reconstruct exact certificates;
the mathematical algorithm allows an exact rational LP solver.

Materialize `SOURCE.tsv` into this directory or use the [source-complete
archive](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80).
Run `sh run.sh | cmp expected.json -`. Python 3, NumPy and SciPy
with HiGHS required. This does not model acceleration, moving
obstacles, changing sensor ranges or action-dependent fault support.
