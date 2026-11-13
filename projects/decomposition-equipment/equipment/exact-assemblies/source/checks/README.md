# E5 bounded actual-cell evidence

Independent finite C implementation. The author supplies the parameterized P proof;
no new Lean certificate, all-model theorem, or arbitrary presentation quotient is
inferred from this checker. It is not a replay of the inherited E3/E4 test suites.

## Frozen dependencies and scope

The exact E4 `e4_completion_cells.py` SHA-256 is
`32cf6e969554d593f76e905339bcca7ac71e17a1da345b390b8030f4bf71cb30`.
Its exact nested E3 `e3_model_cells.py` SHA-256 is
`5941532e760980f0324a958d094e06396010c4d88db7883caa0008ed3edcbfcb`.
They supply actual finite functions/spans, typed graph partitions, scalar monoid,
restriction, actual cells and substitution. Their `main` functions are not called.
No prior source is changed. This checker independently enumerates comparisons,
functions/inverses, tree transports, universal-factor fibres, graph fibres and
congruence closures; it does not call E3/E4 test verdict functions.

Scalar encoding differs from multiplicative mathematical notation: `0` is 1_M,
`1` is the nonidentity involution, and `2` the absorbing nonunit. Coefficient
bijectivity, coefficient bijectivity plus identity scalar, coefficient bijectivity
plus unit scalar, opcartesian factorization, and cartesian restriction are distinct.
Single-graph S cells are used for opcartesian/cross-edge/quotient distinctions;
completed-word W cells are used for actual coefficient transport and tree coherence.
No identification of W's empty word with one empty-graph occurrence is made. W is
not claimed to be a normal completion of S.

## Run

Keep all outputs outside this source directory and every prior protected source:

```sh
python -B checks/run_e5_checks.py --output /tmp/e5-finite-receipt.json
python -B checks/test_e5_guards.py --output /tmp/e5-guard-receipt.json
```

`run_e5_checks.py` verifies its exact closed source manifest before and after the
run, hard-pins both frozen dependencies, unsets inherited `PYTHONOPTIMIZE`, disables
bytecode writes, verifies the actual interpreter mode, and requires byte-identical
normal / `-O` / `-OO` output. Nine semantic mutations must each reject in all three
modes. Receipts are atomically written only outside protected sources. Path,
symlink-parent, symlink-file and hardlink aliases are rejected. A receipt is bound
to the manifest SHA-256 and all six declared source hashes. The manifest is frozen
atomically before final runs; receipt files are not source inputs.

The guard suite mutates disposable source copies only. It tests source/dependency
drift, missing/extra entries, schema mismatch and source symlinks; output aliases;
actual optimization-mode mismatch; and a complete replay with inherited
`PYTHONOPTIMIZE=2`. It never changes an old or final source. Guard receipts are
separate from semantic receipts and do not constitute third-party replay.

## Bounds and claims

* All 16 binary relations on two points, each ordered pair and each of seven
  internal maps from carriers of size 0..2: 1,792 comparison cases. Additional
  actual-span examples retain duplicate witnesses and empty interfaces.
* Surjective noninjective, nonsurjective supported, missed support, equal-cardinality
  nonisomorphism and bijective internal maps. Rel compares support; Span retains
  every old tuple and its actual lift fibre. Nullary diagonal comparisons are
  independently enumerated for old sizes 0..2 and primed sizes 0..3.
* All 22 binary tree shapes with 2..5 leaves, four map regimes: 88 full-tree actual
  coefficient maps. Every proper internal-node contraction permutation and every
  prefix is compared as an actual cell, including scalar and forest. Retained
  local comparisons are checked, not just the root. An independent flat table
  is compared against recursive substitution. All-run versus adjacent-vacuity
  and explicit unary/nullary/empty fixtures are separate tests.
* All functions between sets of size 0..3: inverse fibres are enumerated, not
  asserted from sizes. The identity composite singleton -> two points -> singleton
  demonstrates why root exactness does not reconstruct every retained stage.
* Cartesian restrictions are verified by enumerating actual unique factor fibres;
  direct pullback of a coefficient bijection is bijective. These do not imply
  internal composite-of-restrictions comparison exactness.
* Actual scalar congruence closure for unit-subgroup and absorbing equations;
  actual doubling-section postcomposition yields id_2 = constant_2 at one
  edge-containing active graph, with different actual factor fibres. Extension
  of this equation family to a full VE congruence is P. The finite result does
  NOT claim that an E2 fixed-sort full-VE quotient breaks restriction uniqueness.
* All graphs with 0..4 vertices and partitions into 1..3 named blocks: exact
  reconstruction fibre 2^(number of cross-block vertex pairs). Both no-cross-edge
  and full-labelled-interaction-record repairs are checked. Genuine nonexact
  graph witnesses remain equipment cells. No global scalar or root quotient
  silently deletes local cells, occurrence names, or whole information.

Every reported affirmative status is preceded by a comparison of independently
constructed finite objects. Explicit counterexamples are computed, not accepted
because a fixture carries an expected-verdict flag.
