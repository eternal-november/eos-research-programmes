# Rank sensitive compression formal coverage

2 November 2026

## Main result

The positive compression module now proves an exact decoder at every concrete source, for every finite tree of the original dependent `WitnessedDecompositions.Tree` datatype. It uses the active-component hypothesis of `WitnessedDecompositions.Tree.ActiveSignature`, retains each ordered slot in the old skeleton, and stores group coefficients only at active inputs. It includes inactive positions, nullary vertices and the literal vertex-free identity. This result is stronger than the initial live-tree intermediate lemma; the latter remains a readable preliminary result, not the final scope boundary.

The source is the corrected `full_unital_repair_20261101/lifting/02_exact_full_profile_realization.md`, sections Quotient composition and Joint source fixed cut exactness. These files formalize the coefficient and decoder chain, not its separate minimality theorem or every obligation of the old contract.

## Precise objects

For any group homomorphism h:G→K, two coefficient functions on a profile are equivalent when their h-images agree coordinatewise and, if that profile is a subsingleton, the functions are literally equal. Empty profiles have only one coefficient function. Singleton active profiles retain exact G labels; branching profiles retain their coordinatewise h-images. No finiteness or commutativity hypothesis is used in the group proof. Surjectivity is not silently assumed: the actual quotient carrier is a setoid quotient, hence describes the image quotient. Identifying that carrier with all K-valued branching functions would additionally require surjectivity and is not claimed here.

`ActiveDecoration` is recursive literal data: one coefficient tuple on the active input subtype of each node, together with a decoration of every child, including inactive children. `ActiveDecorationEq` compares each node's whole coefficient tuple and all child decorations. It never replaces a joint record by independent marginals. `activeEvaluate` multiplies coefficients in ancestor order and returns labels at active final occurrences. The fixed tree still retains the original generator, interfaces, order, repeated occurrences, inactive positions and shape.

`ActiveSignature` says that an output is active exactly when at least one of its inputs is active. This premise is independent of the quotient and ensures that every active child has an active final descendant. It does not mean every old slot is active. The node equivalence from `TreeArrayBridge` identifies the active final profile with the dependent sum of active child final profiles over active root inputs. Its inverse retains the original occurrence identifiers.

## Theorems and proof content

- `RankSensitiveCompression.graft_congr`: nonerasing root substitution respects the rank-sensitive relation. A singleton final profile forces singleton parent and child profiles; otherwise homomorphic path products suffice.
- `RankSensitiveCompression.root_lift`: every prescribed whole factor-state tuple lifts at the exact concrete final coefficients. Unary parent labels stay exact; unary child labels stay exact; branching groups use one shared parent and group division for all descendants. Multiplication order is noncommutative-safe.
- `active_evaluate_congr`: recursive factor equivalence induces source equivalence over every original typed tree under `ActiveSignature`.
- `active_all_tree_lift`: induction supplies an actual recursive decoration at any chosen equivalent source, matching every prescribed node factor class. It handles the vertex-free tree directly, rather than inserting a unary vertex or ignoring the empty record.
- `active_exact_tree_decoder`: equivalence between source observation agreement and existence of a whole compatible decoration at that precise source. The reverse direction is the separately proved evaluation congruence.
- `active_quotient_exact`: an explicit instance of `JointQuotientDecoder.ExactDecoder` for actual source and whole-record setoid quotients. The relation is the union over source representatives; the theorem proves it is exact at every representative. It does not assume source-fixed lifting as a decoder hypothesis.
- `branching_proper_compression`: the cyclic-four-to-cyclic-two homomorphism identifies two distinct two-coordinate label functions. This is a kernel-checked properness example, not a state-count extrapolation.
- `edge_fromEdge`, `fromEdge_edge`, `evaluate_eq_path`: the all-slot preliminary decoration model is equivalent to arrays on the same shared input-edge IDs as `JointArrayLifting`, and evaluation is the same ordered path product. The full-active counterpart is proved in `ActiveDecorationBridge`: `activeFromEdges_labels` and `activeLabels_fromEdges` are inverse conversions with inactive edges fixed at one, and `activeEvaluate_eq_path` identifies evaluation at active final leaves. `graph_active_exact_decoder` specializes the positive theorem to the recovered graph-cut signature, using its proved activity condition.

The identity observation applies only to the actual leaf tree with its fixed old identity skeleton. At an inactive leaf the active source profile is empty. At an active leaf it is singleton and the source coefficient must be the group unit. An old unary generator and a vertex-free leaf remain different tree constructors.

## Limits

This module does not prove minimality for the original parity seed, the identity-retraction property of arbitrary old grades, formula-language adequacy, channel-swap saturation, the 256-to-16 two-channel count, the scalar repair hierarchy, a new presentation theorem for the quotient, or a full virtual equipment. It does not preserve literal witness multiplicity, unique lifts or forgotten group labels. The tree index stays fixed in every theorem; transporting old graph data still needs its separate geometry theorem.

These are actual Lean proofs, not empirical verification of robots or physical decompositions. Compiling the modules establishes the stated formal claims relative to Lean's standard logical axioms and imported definitions. The separately captured axiom report contains only the standard `propext`, `Classical.choice`, and `Quot.sound` where used, with no `sorryAx` or newly declared axiom.

## Reproduction

Use the project's pinned Lean 4.35.0 and mathlib dependency. Run `./verify_backbone.sh`; its default Lake build includes both the recovered core and the new `DecompositionBackbone` target, including the full-active bridge, followed by the required axiom audits. Missing modules fail the build rather than being skipped. The source-only theorem files are the deliverables; cached `.olean` files and the installed compiler are build dependencies, not proof substitutes.
