# D1 representative L and C evidence

## Checked scope

`D1FiniteTypedAction.lean` is a standalone Lean 4.35.0 core/Std file. There are three interface objects A, B and C, each with the explicit three-element carrier `Point`. `Perm` supplies a carrier bijection and its inverse laws. `Action = Interface → Perm` is the strict action of the finite group `(S3)^3`; the Python enumeration contains its 216 elements. `mixed` and `second` do not commute. Relations are actual subsets of carrier pairs, transported by inverse coordinates, not merely endpoint names.

The checked declarations give identity/composite/inverse action laws, middle-witness cancellation in relation composition, exact binary primitive validity with a retained Bool decoration, endpoint-typed binary/nullary syntax, independent valid replacement forests, transport/graft compatibility and the target equation for a retained-forest refinement arrow. Rotation invariance is proved rather than assumed. Its *contextual rotation quotient fragment* has induced identity/composite transport. This is not a formalization of the full A3 substitution congruence or all generic refinement-category composition laws: those are covered by the general P proof/adapter. The file also proves a genuine non-invariant relation has no induced quotient function, distinct repeated substitutions remain distinct after transport, and a nonidentity action stabilizes a nullary object.

`D1OriginalAPIBridge.lean` imports the frozen original `WitnessedDecompositions` API, not a look-alike. It constructs an actual finite `Signature`, exact `Assignment` to `RelationInterface.exactCalc`, and `Tree.extend` map. It proves original primitive input-profile/output transport, validity, original `Quiver.Path` identity/composite action and evaluation compatibility. `HEq` in the profile theorem records the dependent endpoint casts, discharged by constructor reflexivity. The file does not assert the original same-base `Calc.Hom` API already encodes arbitrary changed-quiver maps.

The binary Bool-decorated syntax is the sublanguage of the full decorated presentation encoded by `d_k(b(-,-))`; nullary syntax uses the diagonal unit. The general P adapter supplies the full seven-equation presentation and coherent refinement comparisons. No full generic D1 mechanization is claimed.

## Reproduce

Core representative, finite tests, and a Lean mutation negative control:

```bash
LEAN=/path/to/lean-4.35.0-linux/bin/lean ./verify_d1.sh
```

For the original bridge, provide an exact original source project with its frozen `lake-manifest.json`, Lean 4.35.0, matching precompiled dependencies and `research/workstream_C2/lean/RelationInterface.lean`:

```bash
LEAN=/path/to/lean-4.35.0-linux/bin/lean \
D1_ORIGINAL_PROJECT=/path/to/frozen/original/project ./verify_original_bridge.sh
```

The script rebuilds original library sources, emits the original relation-interface module, compiles a fresh core `.olean`, and checks the bridge. Do not run `lake update`. `toolchain_provenance.json` records official pins/checksums. The separate tiny recovery kit can retrieve the official compiler and pinned public libraries. Large binaries/caches are not part of the lightweight D1 deliverable.

## Trusted base and evidence distinction

Both Lean files compile with no errors, custom axioms, `sorry`, `admit` or `native_decide`. The 13 core and 9 bridge printed principal dependency closures contain only `propext` and `Quot.sound`, or no axioms. The complete imported environment is larger; this statement is about actual principal declaration closures, not a claim that every imported mathlib declaration is choice-free. `decide` used on tiny explicit enums is checked reduction, not an unchecked external oracle. We trust the official precompiled Lean release and the matched public upstream dependency cache; these are not independently rebuilt/audited compilers or mathlib artifacts.

`test_d1_finite.py` is supplemental C evidence. It checks all 512 relations on a three-point carrier, all endpoint action composites, exhaustive middle-permutation cancellation and endpoint naturality on all relation pairs, semantic equality for all seven equation templates in the scalar/empty-graph slice (no graph/partition data), independently implemented set and bitset evaluation, repeated slots, parallel arrows with equal totals, refinement composition including nullary insertion, a non-invariant relation and stabilizer loss on object-orbit passage. All 81 interface chains receive base equation tests; all 216 actions are tested on 600 template instances from repeated A-A-A-A and mixed A-B-C-A chains. These are semantic equality/evaluation checks, not literal equation-family membership checks; the P invariance table supplies the latter. It also runs under `python -O`; checks do not rely on removable asserts. It does not replace the general P theorem or the Lean L evidence.

`verify_mutation.py` replaces inverse coordinates by forward coordinates in the actual Lean action and requires a failed Lean check. `mutation_receipt.json` is the delivered pathless rejection receipt. The locally generated `mutation_rejection.log` is intentionally a *failed mutant* transcript, not the final source's build log, and is excluded from delivery. Initial author syntax/elaboration defects were fixed before freezing; only clean final build logs are part of the deliverable.
