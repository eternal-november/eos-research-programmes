# D2 / D3 bounded executable evidence

Run with Python 3.10+ and the standard library only:

```sh
cd checks
python run_checks.py
python replay.py
```

`run_checks.py` verifies `source_pins.json` before imports and emits deterministic
JSON. `replay.py` repeats the clean run and compares normal, `-O`, and `-OO`
outputs byte-for-byte; rejects seven explicit fault injections under normal and
`-O`; rejects a modified **temporary copy** by source hash; and parses every
pinned Python file to reject `assert`-dependent checks. No inherited file is
modified and no network or installed package is needed. A source pin is an
integrity/reproduction mechanism, not a cryptographic claim of trusted origin.

## Scope and provenance

These are **finite C-level checks**, not a new all-degree proof, a Lean
formalization, or acceptance of the original D2/D3 obligations. The mathematical
reports and independent audit determine the separate original-contract verdict.
The code is standalone and does not import or mutate I4 or D1 checkers.

The original obligations are lines 382–412 of
`contract_revision_20261028/final_artifacts/Original_Completion_Contract_v0.1_VERBATIM.md`.
The original C5 flat witness formulas are in the extracted source's
`research/workstream_integration/proof/Semantics_Transport_Factorization.md`
§§1–2. Actual occurrence-tuple refinements come from
`WitnessedDecompositions/SemanticRefinement.lean`. The D1 action and inherited
seven-equation presentation comparison are described in
`d1_equivariant_transport_20261031/theorem.md` §§9.1–9.3. These provenance
sources are read-only mathematical inputs, not runtime dependencies.

### D2

* Exhausts all finite maps and relation pairs with all six cardinalities 0–2:
  **1,331 map triples, 113,171 relation/map cases**.
* Exhausts three-stage paths with old endpoint cardinalities 0–1, old internal
  cardinalities 0–2, and all primed cardinalities 0–2:
  **1,936 map families, 149,578 relation/map cases**.
* Independently enumerates restricted witnesses, the comparison and its actual
  fibres; verifies relation image-hit existence separately from span unique
  lifts. Empty endpoint/internal exceptions are included. A two-by-two
  comparison with fibre sizes `[0,2]` has equal source/target cardinality but
  is not an isomorphism, even though relational equality holds.
* Checks **121** two-named-type map families, **991** unary cases and **11**
  nullary maps. The nullary comparison is diagonal-to-kernel-pair and is exact
  precisely for injective maps; it is not silently treated as a positive path.
* Checks every reduced ordered tree shape through five leaves, namely
  `1,1,3,11,45` shapes, with internal lift multiplicities 0,1,2: **183 cases,
  26,202 nested witnesses**. The same two-apex leaf span is used in repeated
  distinct slots. A shared internal source coordinate is enforced. The
  adjacent-vacuity counterexample proves pairwise local checks alone do not
  justify all regroupings. This finite range is not an arbitrary-tree proof.

### D3

* Uses actual original C5 flat data: whole finite graph and edge set, increasing
  induced restrictions, full typed relation string, ordered partition, scalar,
  and actual original-slot tuple arrows. Presentation completeness is inherited,
  not redefined as semantic equality.
* For three named `Fin 2` interfaces and `H=(S2)^3`, checks **9,216** action laws
  and **55,296** typed composition equations. It includes relation entries and
  entire operations genuinely changed by transport, not merely renamed tags.
* Two repeated nonempty `(K2, diagonal_A)` slots in an actual four-vertex graph
  retain different `(0,0)` and `(1,1)` refinement arrows. The full `H` stabilizer
  has order 8, while the selected `A`-only subgroup stabilizer has order 2.
  Neither is an occurrence-slot permutation. A six-vertex graph exercises
  actual nested substitutions and the flat values of the seven inherited
  equations.
* The two-alias interface-groupoid equivalence retains both `(h, full tuple)`:
  **16 hom bijections, 256 arrow images, 16,384 composition squares, 4,096
  associativity triples**, plus explicit quasi-inverse naturality and triangle
  checks. The fixed-diagonal finite refinement slice has two objects (scalar
  0/1), and its retained-symmetry endomorphism homs have 16 actual arrows each.
* Rigid charts into `B(S2)` have a discrete iso-comma with two seam objects
  (`id`, `swap`), whereas the coarse class pullback has one object. The
  comparison fibre has size 2: the coarse class loses unique seam lifting.
* On `Fin 3`, transpositions `P=(01)` and `Q=(02)` are conjugate. Actual C5
  empty-graph binary children `(P,P)` and `(Q,Q)` lie in the same orbit, yet
  substitution gives `(P,P,P,P)` versus `(P,P,Q,Q)`, different diagonal orbits.
  This is an interface-only obstruction to independent orbit substitution;
  the scalar action is trivial and all scalars are zero.

## Files

* `d2_finite_checks.py`, `d3_finite_checks.py`: independent finite models/checks.
* `run_checks.py`: source-pinned deterministic entrypoint.
* `replay.py`: deterministic, optimization, fault-injection and tamper controls.
* `source_pins.json`: SHA-256 integrity manifest for the four executable sources.
* `finite_results.json`, `replay_results.json`: saved output of the two commands.

All source pin changes require regenerating and replaying both result files.
