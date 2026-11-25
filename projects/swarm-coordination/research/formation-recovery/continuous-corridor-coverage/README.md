# Continuous corridor coverage

[Proof and scope](Continuous_Corridor_Coverage.tex) · [Lean pointwise atoms](NoGap.lean).

```sh
set -o pipefail
OPENBLAS_NUM_THREADS=1 python -B replay.py | cmp result.txt -
lean NoGap.lean
```

Numerical replay used SciPy 1.17.0 with HiGHS. The code compares the
predetermined-cell programs with a simple-path oracle using the same
convex-cell definitions but independent route enumeration. Lean checks
two real-order implications, not solver output or the entire path theorem.
