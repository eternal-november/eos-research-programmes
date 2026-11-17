# Initial-tranche Lean 4.35 migration

Current toolchain: Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, matching the established prior formal environment.

The initial 4.19 choice was a newly selected familiar version, not recovery of the prior environment. No source requirement justified downgrading. Its source, build and independent-review evidence are preserved separately as historical evidence, not evidence of 4.35 compatibility.

Migration changes: use the new module/public-section syntax; remove unused simp arguments; adapt the two literal Kleisli/coKleisli composition comparisons to mathlib's new object/hom wrapper structures by projecting `.of`. The underlying operations, square predicates, Para cells and coherence equations are unchanged. The source crosswalk clarifies this representational adaptation. No theorem was weakened to an assumption.

For the initial tranche, build and all 31 named-theorem axiom audits passed on 4.35. Independent 4.35 fresh-source replay and statement-delta review passed within the declared partial scope. That review identified a stale axiom summary: all eight FixedEffects theorems additionally depend on Classical.choice. SOURCE_CROSSWALK.md now matches the actual audit; no Lean source or dependency pin changed during this documentation correction. Cached pinned dependency objects are used; no from-source rebuild of all mathlib is claimed.
