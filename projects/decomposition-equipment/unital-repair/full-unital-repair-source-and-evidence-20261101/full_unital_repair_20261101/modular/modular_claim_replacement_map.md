# Full unital modular claim replacement map

1 November 2026. Integration guide. No original artifact is edited by this map.

## Exact claims to replace

Old source: `i5_joint_repair_20261031/modular_repair_draft.md`.

* Sections 1 and 3: the positive grouped coefficient equations and fibre-product formulas are retained. For the vertex-free identity cut use the actual-unit predicate. Product equality of fibres remains valid, but their nonemptiness and projection surjectivity do not. New section 1 gives the precise empty-fibre case.
* Section 4 completeness: retained with the explicit direct U argument in new section 2. No nonemptiness assumption is needed for this part.
* Section 4 optimality: withdrawn without an added hypothesis. New section 3 proves reflection when the local seeds already determine their respective actual U predicates. It treats positive cuts by fixed-source lifting and U by seed invariance. Its semilattice example proves the old unconditional formula false even when the combined local partition is complete.
* Section 5 selected symmetric M_k result: a specific product equality may still be deduced from independently proved local and global full-profile exactness. H itself does not determine the true unit, so the new generic optimality theorem cannot be applied directly. Use the corrected main observation-theory proof, not the old nonempty-fibre argument.
* Section 5 asymmetric H versus indiscrete-channel example: do not reuse its assertion that the ignored channel's full-unital repair stays indiscrete everywhere. Replace the general branching modular failure control by new section 5, which proves the appropriate high-rank collapse for the group family and supplies a genuine all-N-at-least-2 exchange failure.
* Section 6 shared scalar separator: retain literal pullback and exact separator gluing, but add the local-U seed condition to its generic coarsest-repair conclusion. New section 4 separates completeness from optimality.
* Section 8 eight-element same-cut example: the old local partitions fail U because the old Q merges the identity with t. Replace K by its external unitization K plus; keep the old e as an internal idempotent; add fresh {1} singleton to both partitions. Use exact rather than ignored private factors. New section 6 proves all N equals 1 profiles and arbitrary finite generated depth, and explicitly disproves coordinatewise branching stability.
* Section 9 coefficient presentation and retained-forest normalization: retained at its stated scope. It does not create empty-cut witnesses at nonidentities or justify arbitrary cut projection lifting. Distinguish normalization of a separately retained factor operation from erasure of an entire marked cut vertex.

## Generic repair calculus changes relevant here

Old source: `i5_joint_repair_20261031/repair_calculus_draft.md`, section 5.3 and final channel-product paragraph. The generic finite/image-finite repair theorems already accommodate empty fibres and nullary cut tuples. The invalid step is the family-specific assertion that every full-unital fixed-skeleton channel fibre is nonempty. Do not claim full-unital C acts channelwise on arbitrary product seeds, or reuse positive-cut round counts unchanged. The own-U-aware seed condition supports an optimum theorem through new section 3; it is not a blanket elementary-splitter equality without a separate argument.

Old source: `i5_joint_repair_20261031/i5_joint_repair_theorem.md`, sections 7.3 and 10. Preserve the positive-tree product argument only with its stated restricted predicate; integrate the corrected U-aware comparison and the two distinct modular failures. No all-profile scope reduction is licensed.

## I1 comparison boundary

The operation-level coefficient presentations, conservative retractions, declared cross-channel interchange and separately retained occurrence-forest normal forms do not depend on the false zero-cut lift. They remain available at their proven scope. All claims of literal marked-cut lifting or label-blind existence that include the vertex-free tree need an identity guard or a proved unit-reflection/lifting condition. The dedicated lifting-map repair handles that condition. No new unrestricted I1 acceptance follows merely from this modular note.

## Evidence and status

`full_unital_modular_repair.md` is the author proof. `verify_modular_full_unital.py` and `modular_full_unital_results.json` are bounded executable support; `geometry_replay_audit.md` records independent replay, enumeration counts, rejected mutations and the found-and-fixed explicit-U checker gap. The independent K plus construction and checker are in the sibling checks directory. An independent geometry subagent validated the all-profile group proof; the main repair reviewer read the full note and passed its mathematical proofs without correction. These are agent-managed proof reviews, not independent human certification. No Lean kernel certification, original-source rewrite or public upload is claimed.
