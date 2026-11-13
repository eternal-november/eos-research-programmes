# Original-calculus dynamic target (27 October 2026)

This is an additive formalization against the unchanged source package and its pinned Lean 4.35.0/mathlib dependencies. Import `WitnessedDecompositions.Dynamic.Bridge`; the original public root module and lake configuration are unchanged.

## Kernel-checked scope

- `Graph.lean`: arbitrary graphs with distinct actual event records, graph maps, span assignments on the **original** `Component`, and recursive fine-boundary compatibility.
- `Occurrences.lean`: families assembled through the original `Path.Slot` / `Path.slotExpand` bijection. Ordered typed coordinate words are used only for extensional proofs, not as substitute syntax.
- `MapOperations.lean`: actual coordinate-map composition with full original `Calc` unit and associativity laws. No nullary or repeated-color restriction.
- `Compatibility.lean`: closure of the fine-boundary equations under arbitrary occurrence substitution; empty inner profiles supply equality of their exposed boundary legs.
- `Tuples.lean`: actual sortwise compatible-tuple graphs, full equivalence with compatible map families, and canonical singleton graph isomorphism. The empty tuple graph is the actual boundary graph, not a terminal singleton. Nested pullback carriers are not identified definitionally across reassociation.
- `Target.lean`: `Assignment.calculus`, the actual boundary-compatible dynamic `Calc`, retaining **all** graph maps, including nonexact maps; `operationEquiv` identifies its prescribed fibres with all boundary-preserving witness maps. Nullary fibres are inhabited iff the legs agree, are subsingletons, and their actual witness is the common leg. Nullary exactness is precisely isomorphism of that leg. Identity witnesses are exact.
- `Bridge.lean`: original `Tree.extend` and `Tree.homEquiv`; original `Presentation.extend` with a premise comparing the full interpreted graph maps; descent iff that premise holds; original free/presented `SemanticRefinement.functor`. The original declared-equation quotient is not replaced by a semantic-kernel quotient.

No finiteness hypothesis is necessary for these proofs. Finite graphs are included. `Graph.isIso_iff_bijective` equates exactness with bijectivity on both states and actual events.

## Verification

With the pinned `lake` on PATH, from the package root:

```sh
bash scripts/verify_dynamic.sh
```

In this restored workspace, first run `source ../.toolchain/env.sh`. Do not run `lake update`.

The dedicated axiom audit checks the actual target, source bridges and nullary classification. Its allowed standard Lean axioms are `propext`, `Quot.sound`, and `Classical.choice`; no new axiom, `sorry`, or `sorryAx` is used. Choice occurs in the sortwise-bijection/inverse characterization and the existing generic presentation quotient implementation, not in the dynamic target calculus itself.

The independent fixture suite exercises nonterminal retained empty boundaries, unequal legs, nonexact nullaries (including event-only collapse), all-empty substitution, repeated colors with different slot maps, parallel-record distinction, a genuinely nonempty declared equation and rejected event-permutation equation, and unequal refinement forests with the same substituted root.

## Explicit boundary of this checkpoint

This checkpoint does **not** claim the later general exact-substitution theorem, execution/time comparison, interface-change theorems, CFG/decision procedures, or physical implementation correctness. Those remain later milestones. It also does not supply an assignment for every historical presentation automatically: a concrete assignment and its stated equation proof are required by the source bridge.
