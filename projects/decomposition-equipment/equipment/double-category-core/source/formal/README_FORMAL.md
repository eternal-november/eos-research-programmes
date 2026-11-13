# E1: concrete checked core-facing fragment

## What is checked

`E1RelationEquipment.lean` implements the Nat-decorated relational virtual-equipment fragment described in the E1 classical text, using the unchanged original `RelationInterface.Interface` quiver and original `Quiver.Path`:

- Interfaces have arbitrary small carrier types; vertical maps are arbitrary typed functions. Horizontal components are actual relations. A multicell has the stated outer boundary functions, the inclusion of the evaluated source relation into the boundary pullback of the output relation, and an **independent retained natural-number witness scalar**. Only the inclusion proof is proof-irrelevant.
- `restrictionEquiv`, `restrictionCompose`, `restriction_factorization`, `restriction_unique`: complete-cell cartesian factorization for every typed source path, zero included. `restriction_natural` proves compatibility with any supplied semantic substitution row. `restrict_identity` and `restrict_composite` are the split inverse-image coherence.
- `contextSubstitute` is actual substitution at a selected occurrence in arbitrary typed prefixes and suffixes, adding the scalar. `ContextualOpcartesian` quantifies bijectivity over all these contexts and arbitrary external boundaries. `marked_iff_contextual` proves that the globular mark “evaluated relation equals output AND scalar zero” is precisely this universal property, not a renamed equality predicate.
- `unit_is_contextual`, `unitContextEquiv`, `unitContextEquiv_is_substitution` prove full universal nullary-unit substitution. `primitive_not_contextual` and `primitive_not_unit` keep scalar-one nullary primitives legitimate but nonuniversal.
- `coreCalc` is a new instance of the **original** lawful `Calc`, obtained by totalizing the concrete equipment's globular `Cell` fibres. The full old occurrence-indexed substitution is used, including `Path.sum` over independent input occurrences. `coreFiberEquiv` identifies its exact image as **all globular cells** with the chosen relation horizontals, retaining the scalar. No all-cell/exact collapse occurs.
- `exactLift` is an original strict `Calc.Hom` from the pre-existing exact relation calculus. `marked_image` identifies its image; `exactLift_injective` and `exactRefinement_faithful` reflect operation and whole refinement-tuple equality. `refinementComparison` and `exactRefinementComparison` use the original B2 `SemanticRefinement.functor`. The separate `forgetScalar` deliberately forgets the scalar; `forgetScalar_kernel` explicitly identifies its nonfaithful operation kernel.
- `Action` is the checkable preservation class of a carrier equivalence at each interface. `actPath_evaluate` works at every arity, `actCore_marked_iff` preserves and reflects the mark, and `actCore_identity` / `actCore_composite` prove coherence for identity and two successive changes. Noninvertible restrictions still exist; they are not silently claimed to preserve exactness.
- `equipmentSignature`, `equipmentAssignment`, `freeCoreMap` and its surjectivity theorem are an **exhaustive all-witness API regression bridge** to the old `Signature`, `Assignment` and `Tree.freeCalc`. This is not a substantive smaller presentation, not a quotient/presentation equivalence, not a free-equipment theorem, and not reconstruction. The substantive presentation theory remains P/imported prior work.

`E1FiniteExamples.lean` supplies three distinct interface tags, multiple horizontal components on the same endpoints, parallel cells, nonidentity boundary factorization, two noncommuting changes, a legitimate nonuniversal binary witness, a marked universal binary witness, bijective reindexing, a nonuniversal primitive versus a universal nullary unit, and a unit in a nonempty prefix **and** suffix. It also checks the original exhaustive signature bridge on the nonuniversal witness.

## What remains classical rather than Lean

This is the expressly required **core-facing typed fragment**, not a Lean formalization of the entire equipment 2-category. Construction of every arbitrary nonglobular row from individual constituent multicells, full virtual-double-category laws at that generality, all normal morphism/2-cell laws, graph-and-span model, arbitrary chosen-versus-unchosen comparison, and the general witness-sensitive presentation package are proved in the P document. `precompose` accepts the semantic relation map and scalar induced by a row; it does not itself formalize that whole row constructor. The unbounded restriction/unit/core/action theorems above are genuinely proved and are not inferred from bounded enumeration.

## Reproduction

Run from the delivered source directory:

```
python3 formal/verify_fresh.py \
  --toolchain /path/to/lean-4.35.0-linux \
  --upstream-project /path/to/pinned-public-dependency-project \
  --work-parent /writable/fresh-runs \
  --output /writable/e1-fresh-result.json
```

The upstream project must already contain the nine public dependency sources/caches named in `original_source/lake-manifest.json`. The runner checks **every actual git revision and clean tracked source**, exact original lock hash, and the official Lean version/commit. It does not install, download, run `lake update`, or reuse any previous original/E1 project object. It creates a new project, copies only source, checks copied source hashes, and only symlinks the public dependency directories. This is not an independent source rebuild/audit of Lean or all mathlib.

The runner builds **every bundled original Lean module**, including `RefinementComparison`, `RefinementLifting`, `RefinementFunctoriality`, and `WeightInvariant`; then C2 `research/workstream_C2/lean/RelationInterface.lean` into its matching `.lake/build/lib/lean/research/workstream_C2/lean/RelationInterface.olean` import path; then the two E1 modules. Each printed named closure permits only `propext` and `Quot.sound` (or no axioms), never `sorryAx`, new axioms, `Classical.choice`, or native-decision trust.

The runner executes four real semantic mutations of the final frozen Lean source: erase a restriction's scalar, erase the sum of inner witness scalars, erase contextual substitution's inner scalar, and weaken exact equality to mere containment. Each mutant must fail proof checking, with import/root failures explicitly rejected as false evidence. Its JSON receipt records all source hashes before/after, exact commands/return codes, logs/hashes, compiled object hashes and named axiom closures.

The independent Python model/checker and its normal/`-O`/`-OO` receipts are under `checks/`. Their finite bounds are separate from the unbounded Lean theorem quantifiers. The scalar list used in finite tests is a sample, not a claimed finite substitution-closed model of Nat addition.

## Source custody

`original_source/` contains unedited source/configuration copied from the frozen original workstream archive; no original proof is edited. Its correspondence is recorded by the fresh runner's `copied_original_source_hashes`. Original dependency lock SHA256: `0e4afebb985207e83e2a2fdf3d42281f9986e939ebc31084eaa5f8c3479c22cc`. Mathlib pin: `56a005855ea17e0b0958f73ec801ae140b0a1679`. Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
