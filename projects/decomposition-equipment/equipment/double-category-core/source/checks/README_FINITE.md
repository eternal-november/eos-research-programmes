# Independent finite E1 relational-equipment checks

Run locally with Python 3 standard library only:

```sh
cd /workspace/shared/e1_equipment_core_20261031/checks
python3 test_e1_finite.py --output finite_results.json > finite_run.log 2>&1
```

`e1_finite_model.py` is an independent executable implementation of the same
Nat-decorated relational slice as `formal/E1RelationEquipment.lean`. It does not
import Lean-produced answers. Objects have explicit tags; relations retain their
actual endpoint types and pairs; cells retain the whole ordered source path,
output relation, two vertical functions, and a natural scalar. Only the validity
condition is proof-only. Scalars are not truncated by the model.

## Bounds and observations

- All paths through arity 2 on the three carrier sizes 0, 1, 2; plus all relation
  paths through arity 3 on mixed tagged two-point interfaces A, B, C, A.
- The recursive composite of every one of 4,901 complete typed profiles is
  checked against a separate full-compatible-tuple oracle. At arity zero that
  oracle retains a single boundary coordinate, producing the diagonal.
- Every junction of those profiles is tested for unit insertion, including empty
  prefix and suffix; all two-point outer relations and all available boundary
  functions are checked. Cell scalar values 0, 1, 2 remain distinct and unchanged.
- Restriction tests select one representative for each distinct source endpoint,
  target endpoint, source arity, and evaluated relation: 113 representatives.
  For those, all four vertical functions in the typed factorization are varied,
  every two-point target relation is checked, and both factor/unfactor roundtrips
  compare entire actual cells at scalar values 0, 1, 2. This test-case selection
  is not a quotient of paths or cells in the model.
- All composable pairs of maps between sizes 0, 1, 2 satisfy chosen-restriction
  coherence, with maps composed in the correct order.
- All vertexwise bijection families on all tested profiles preserve and reflect
  the actual globular marking `composite = output and scalar = 0`.
- All function families on every binary mixed two-point profile preserve valid
  cells and scalar witnesses. A stored explicit counterexample shows that this
  action need not preserve the exact marking.
- Real two-level cell substitutions include independent nullary child profiles
  and repeated equal component slots; both associations compare complete cells.
  Separate refinement-row checks retain different occurrencewise scalar tuples
  even when their aggregate is the same.

`finite_results.json` records exact counters, bounds, source SHA256 digests, and
negative-control witnesses. The runner checks that its source bytes and model
source bytes do not change during execution, records both start/end hashes, and
atomically replaces the result JSON only after the complete run succeeds.

## Semantic negative controls

These are executable changed operations on explicit data, not comments or
renamed theorem checks:

1. Erase scalar witnesses to zero: distinct parallel cells collapse.
2. Replace nullary evaluation by the empty relation: the tuple oracle disagrees
   on the inhabited two-point interface.
3. Reverse the order of composed vertical maps: noncommuting flip/constant maps
   produce a different restricted relation.
4. Transport the old exact flag under an arbitrary internal map: the reindexed
   composite is empty while the restricted output is nonempty, so the computed
   actual marker disagrees with the transported flag.

## Limits

This is bounded executable evidence, not an unbounded proof. In particular,
checking that scalar-one substitution does not hit scalar zero for trial inputs
0 through 19 is only a finite check; Lean supplies the unbounded Nat theorem.
The complete classical 2-category, graph-partition model, and arbitrary-size
universal laws are not asserted to follow from these finite counts.

## Optimization-safe reproducibility

All semantic-critical model conditions and test failures use explicit raises,
not Python `assert` statements that disappear under optimization. The final
verification runs the identical source normally, with `-O`, and with `-OO`.
`finite_manifest.json` compares their complete substantive JSON results, excluding
only elapsed time; separate atomic result files and logs are retained.

`test_e1_guards.py` additionally makes temporary private source copies and checks
nine deliberate failures: a source mutation during execution, an incorrectly
accepted negative control, and an invalid cell scalar, each in all three modes.
The expected subprocess exit is nonzero; `guard_results.json` records the actual
error output and confirms no successful result was emitted by the source-mutated
run. It never mutates the deliverable's source files.
