# Transferable settlement rights: Lean proof

This file checks the [transferable settlement window argument](../Transferable_Settlement_Rights.tex) for views of a single immutable history. A view takes the union of each delivered grant's exposed IDs and separately certified contiguous settlement prefixes. A counted ID is exposed but not retired by a certified prefix. An above-frontier individual receipt does not by itself retire a counted slot.

- `SwarmSettlement.all_views_right_unique_iff` characterizes injectivity of right labels on counted IDs in every view. `two_atom_counterview` yields the explicit two-delivery counterexample if a required prior settlement is missing. The premises are self-exposure, strict same-right certification chronology, and unique times on each right. Time may be a per-right ordinal; nothing requires a total grant order across unrelated rights.
- `SwarmSettlement.published_issuer_width_bound_of_no_holes` computes issuance and certified marks as maxima over the delivered atoms, normalizes issuance as the larger of the two, and proves the sum of the resulting issuer window lengths is at most the number of rights. The additional premises specify positive consecutive issuer slots and prefix semantics. The proof derives interval attainment from the no-hole premise rather than assuming a width bound.
- `SwarmSettlement.normalized_width_mono_extra_certification` shows that extra authenticated prefix evidence cannot increase width when the normalized issue mark rises along with it. This does not license extra grant-only issue visibility without its evidence.

The proof does not verify how cumulative prefix certificates are produced or authenticated, spending authority is transferred, independent arrivals are buffered, or physical settlement occurs. The prior-spend condition is proved sufficient and necessary for per-right uniqueness, not necessary for a total width bound in every possible encoding. Above-frontier receipt membership, liveness, and metadata size are not certified here.

Use Lean/Lake 4.35.0 (Lean commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) on PATH and a Lake project with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. If its dependencies are not built, prepare the imports in that project first; the replay expects their compiled modules.

```sh
bash replay.sh /path/to/pinned/lake/project
```

The replay compiles to a temporary directory, checks the pinned revisions, and audits 17 declarations. See `KERNEL_REPLAY.log` for the receipt. No Swarm or Contextual Composition modules are imported.
