# E3 bounded actual-cell evidence

`e3_model_cells.py` implements two separately typed cell calculi:

* graph cuts over the finite groupoid with objects 0,1,2 and S3-labelled arrows;
* graph cuts with actual finite spans, functions, boundary-marked compatible
  tuples, and coefficient functions, including noninvertible vertical maps.

All witnesses retain full source paths, target wholes, actual ordered partitions,
and a scalar in C2 with an absorbing zero. Span cells additionally retain every
coefficient value. No operation is represented by only a truth value or label.
The span tuple convention follows the completed E2 actual-cell regression, but
this package does not import or execute E2 code. It adds an independently typed
primary groupoid calculus and tests the comparison between the calculi.

The principal six-vertex fixture is the exact C1 fixture: edges
01,12,13,24,34,45; blocks (0),(1,3),(2,4),(5); the alternate whole adds edge 05.
The two middle nonempty components receive opposite proper binary refinements.
The interfaces are 0,1,1,1,2; the outside grades are a=(01) and b=(12), with
identity middle grades. Graph grades therefore do not silently commute.

Checks cover all S3 grade restriction combinations, actual cartesian factor
fibres, universal unit insertion at every position, repeated unit coherence,
three-row substitution with nullary runs, successive interface changes, original
profile bijection and witness/refinement reflection, and the actual invertible
comparison between graph-grade restriction and full Span restriction. Exact
assembly is tested by enumerated factor fibres; nonuniversal witnesses have
explicit colliding factors. Nonrepresentability is checked by the two distinct
cross-edge target wholes against every possible two-vertex candidate graph.
The P proof handles all other sizes and arbitrary contexts; finite evidence does
not replace that proof or the separately checked typed core bridge.

## Source custody and execution

`source_scope_manifest.json` is frozen atomically only after the finite sources
are final. The runner checks every recorded hash before and after execution,
requires the four substantive finite source files, and refuses source-tree,
symlink or hard-link output aliases. It writes an atomic receipt outside the
source tree. A parent final artifact freeze may additionally bind these bytes
alongside the mathematical proof and formal bridge.

Run (choose an external output file):

```
python -B checks/run_e3_checks.py --output /tmp/e3_finite_receipt.json
python -B checks/test_e3_guards.py --output /tmp/e3_guard_receipt.json
```

The runner clears inherited PYTHONOPTIMIZE, invokes normal, -O and -OO modes,
verifies the expected optimization flag inside each actual subprocess, and requires
exact identical baseline JSON bytes. Eight genuine semantic code
mutations run in every mode: missing grade inverse, sorted partition slots,
erased graph scalar, deleted nullary scalar, forgotten comparison scalar,
unordered refinement tuples, missing pullback witness, and erased unary graph profile. Each must fail an actual cell or factorization test, not a filename check.
All checks use explicit exceptions, so optimization does not disable them.
The guard suite tests nine protected destinations, four source-manifest/drift
failures, and the three actual interpreter optimization modes in disposable copies.
