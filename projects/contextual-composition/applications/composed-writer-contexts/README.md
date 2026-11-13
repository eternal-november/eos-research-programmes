# Composed accumulator contexts: braid obstruction and repair

This strict finite example addresses the catalogue's **composed contextads** direction without claiming a general construction for arbitrary contextads.

Two pairwise-valid semidirect distributive laws need not coexist with an independent swap of their mode contexts. The exact criterion is commutation of their actions. Two reversible linear operations on binary wires fail it, and the attempted 16-element composite is nonassociative. Retaining the generated S3 action repairs the construction with 6 mode states and 24 combined states, minimal under arbitrary input/output probes.

The manuscript proves the criterion and scope-qualified minimality. This is classical semidirect-product/distributive-law mathematics applied as a checked example, not a novelty claim or a Lean-formal result. It complements rather than replaces the existing supplied-law relative construction.

Read the [manuscript](Composed_Contexts_Braid_Obstruction.tex). Run `python3 check_composed.py`. It uses only the standard library.

The repair does **not** preserve full histories, cost, or intermediate traces; it preserves the exact resulting affine action only.
