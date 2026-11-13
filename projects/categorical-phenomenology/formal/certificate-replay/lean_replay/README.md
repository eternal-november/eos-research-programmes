# Literal Lean replay of stored list certificates

## Verified result

The original generated certificates were translated step for step, not replaced by hand-written proofs of the same statements. Lean 4.35.0 accepted every translated original bundle.

- 23 original bundle files, of which 19 are nonempty and 4 are empty budget-exhausted bundles.
- 89 library-entry occurrences and 302 held-out-proof occurrences accepted.
- All 1,605 recorded rewrite-step occurrences preserved in their original branch and order.
- Every accepted declaration reports **no axioms** using `#print axioms`.

These are **occurrence counts with repeats across methods/budgets**, not counts of distinct discoveries or new mathematical statements. The replay covers the original `experiment/results/*_proofs.json` bundles. It does not cover the later screening-followup bundles or old snapshots.

The focused guided bundle contains 5 library entries, 15 held-out proofs, and 88 recorded rewrite steps. In particular, `lib_lemma_003` replays the generated proof of

    rev(app(rev(X), Y)) = app(rev(Y), X).

Its crucial induction step keeps the tail fixed and instantiates the generalized parameter `Y` with `cons(head, Y)`. `held_rev_nested` replays the stored compositional held-out proof of

    rev(app(rev(app(X, Y)), Z)) = app(rev(Z), app(X, Y)).

It uses the generated lemma at exactly the recorded root path with `X := app(X,Y)` and `Y := Z`. It is not a separate manual reproof.

## How the replay works

`translate.py` is a deterministic Python-standard-library exporter. It does not import the original checker or search code.

1. Define polymorphic finite-list `app` and `rev` recursively in Lean. The four primitive rewrite rules are theorems proved by definitional reflexivity, not assumed axioms.
2. Translate each source AST to those definitions over `List α`, for arbitrary `α : Type u`.
3. Emit one explicitly typed equality witness for every stored rewrite. Instantiate the named source rule, reverse it with `Eq.symm` if requested, and lift it at the exact recorded AST path with `congrArg`.
4. Join the witnesses with `Eq.trans` and combine the two recorded normalization chains.
5. Translate a source induction certificate using structural list induction, generalizing all other original parameters. The induction tail is rigid; only the other parameters are instantiated.
6. Prove library entries in source order. Held-out successes are not added to the usable rewrite library.

There is no `simp`, `rw`, `native_decide`, theorem search, `sorry`, `admit`, custom axiom, finite-model acceptance, or imported list theorem in the generated proofs. `import Init` supplies Lean's basic definitions, equality, and inductive types. Lean's ordinary elaborator and kernel still perform their normal type checking and definitional reduction.

Each generated `.lean` file records the original bundle SHA-256. Its `.trace.json` records source equations, the before/after AST of each step, rule, direction, path, substitution, and source line. `validate.py` separately flattens the original certificates and checks equality with the emitted rule/path/order records before compiling.

## Verification and falsification checks

`validation.json` records the version, input/output hashes, counts, per-bundle exit codes, and test results. `checked/*.lean.log` contains the full Lean axiom audits.

- 17 exporter unit tests pass, covering exact trace preservation, malformed paths/rules/directions, omitted critical steps, freshness, rigid-tail induction, forward/circular references, duplicate entries, ill-typed terms, unavailable held-out lemmas, identifier injection, reverse rewrites, and generic structural induction.
- Three additional positive Lean fixtures pass: reverse-direction rewriting; a generalized element parameter sharing its spelling with a list variable; and a consistently alpha-renamed copy of the guided bundle. These are translator tests, not claimed discoveries.
- Lean independently rejects all three deliberately corrupted generated files: an incorrect induction-hypothesis parameter, reflexivity substituted for the nontrivial induction step, and an incorrect argument in the held-out reuse of the generated lemma. The rejected examples and compiler diagnostics are in `negative_tests/` and are intentionally not compilable.
- The original Python checker's 16 tests were rerun successfully. That is supplementary evidence; the Lean exporter and Lean acceptance do not rely on that Python checker accepting the bundles.
- All original certificate files are unchanged.

## Trust and scope

Lean checks the actual generated theorem statements and proof terms against the recursive definitions. The Python checker is no longer the sole soundness boundary for these particular accepted proofs. The exporter itself is **not formally verified**. Faithfulness of AST interpretation and trace translation remains a reviewed/tested engineering boundary, supported by explicit intermediates, source hashes, recorded substitutions, independent trace comparisons, and negative tests. A malicious or buggy exporter could in principle emit a different true statement, so Lean acceptance alone is not proof of faithful translation.

This is a result for the fixed finite-list equational calculus and the stored certificates. It does not establish correctness or completeness of proof discovery in general, absence of bugs in every input case, benchmark superiority, a new proof-search algorithm, or mathematical/source novelty. The separate resource-observation mathematics is not established by these list replays.

## Reproduce

Use an existing Lean 4.35.0 installation and Python 3. No package manager, mathlib, extra Python package, or network access is required for replay.

From the parent directory containing `lean_replay/` and `experiment/`:

```sh
LEAN_BIN=/path/to/lean python lean_replay/validate.py
```

For the focused guided bundle alone:

```sh
python lean_replay/translate.py experiment/results/guided_10000000_proofs.json lean_replay/Guided.lean
/path/to/lean lean_replay/Guided.lean
```

The local toolchain used was:

- Lean version: `4.35.0`, x86_64 Linux, Release.
- Commit: `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- The validator resolves the executable from `LEAN_BIN`, then `PATH`, or an explicit `--lean` argument.
- Executable SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
- Official distribution: [Lean 4.35.0 Linux release](https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst).
- Distribution archive SHA-256, matched to the retained official release metadata: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.

The 594,481,375-byte toolchain archive is deliberately not included in the compact proof artifact. The source package contains original JSON inputs, the exporter, tests, Lean source, trace maps, and validation logs.

## Portable checkpoint provenance

This delivery copy replaces environment-specific paths with relative paths and resolves Lean through `LEAN_BIN` or `PATH`. The validator, README, normalized command/diagnostic logs, and manifest changed from the internal checkpoint. Original certificate bytes, their SHA-256 values, generated Lean proof text, and trace maps are unchanged. Logged `<LEAN_BIN>` denotes the compiler selected for that run.
