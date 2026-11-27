# Time bounds for wide corridor intervals

[Model, lower and upper certificates, and scope](Wide_Corridor_Coverage_Bounds.tex).

```sh
set -o pipefail
OPENBLAS_NUM_THREADS=1 python -B projection.py | cmp result.txt -
```

The checked-in comparison imports the sibling continuous-corridor-coverage
reference. The clean backup instead includes an identical copy as
`exact_ref.py`. Same-information numerical route enumeration uses SciPy
1.17.0; the rollout and independent chord checker use exact fractions.
Out of 77 wide ascending cases across three meshes, all 231 lower
bounds matched the route comparator; 224 rollouts were certified by
their chords. Additional controls test a disconnected false arrival
and two overconstrained crossing orders.

[Exact finite-cell certificates](exact-continuous/README.md) supplies the
continuous completeness argument and validates route optimum and failure
certificates with rational arithmetic rather than accepting LP statuses.
