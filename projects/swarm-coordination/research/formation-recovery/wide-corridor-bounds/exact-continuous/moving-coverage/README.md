# Exact coverage of a moving inspection interval

[Model, sharp bound and certificates](Moving_Coverage_Cut.tex). A static
coverage check at the start, turn and finish says a modeled inspection
interval can travel 7 units out and back. Continuous coverage with the
same speed and radio constraints limits its peak excursion to
`(7 + sqrt(33))/2`, about 6.3723. The moving robot must stay in range of
the stationary robot's sensing footprint until the whole interval has
passed the coverage seam. A piecewise-linear path attains the bound.

The replay uses rational certificates for lifts of the
previous corridor cells into time and configuration. It matches the
closed-form threshold on 25 rational peaks with 307 route checks.
No sensor field claim, acceleration limit, changing unknown fault
law or independent contract case is implied.

Materialize `MOVING_INPUTS.tsv` in this directory, or use the [Space
source-complete archive](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80).
Run `sh run.sh | cmp expected.json -` (the archive names them
`run-moving.sh` and `moving_final.json`).
Python 3, NumPy, SciPy with HiGHS; Lean 4.36.0 and Mathlib check the
scalar endpoint algebra in `MovingZone.lean`.

[Late notice of the owed window](branch-notice/README.md) separates
physical feasibility from the common-prefix restriction. Near the
physical limit, starting to move before notice helps only if the
late-window branch can still retreat in time.
