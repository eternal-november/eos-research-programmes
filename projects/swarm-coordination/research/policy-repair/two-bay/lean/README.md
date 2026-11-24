# Two-bay distributed repair: Lean proof

Three Lean modules use pinned Mathlib, with no Contextual Composition or Swarm project imports. Lean 4.35.0 (commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc); Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.

- PolicyTables: one uniform A bit, a physical two-bay routing swap and a B table over arbitrary local modes. It identifies the compatible set, all unary projections, equality of projected relations, and the two-mode witness for failure of the unchanged B table.
- PolicyNormalForm: for Fin (n+1) modes, fixes the first mask entry at false and proves that Boolean tails on Fin n biject with the distinct compatibility relations.
- PolicyTableCount: derives 2^n distinct relations and exactly n bits for the chosen interface: a fixed-width binary code must answer compatibility for every fixed B table. It includes the membership-to-injectivity bridge and a matching decoder. No running-time or unrestricted synthesis claim follows.

Put Lean and Lake 4.35.0 on PATH. Run:

    ./replay.sh /path/to/pinned/lake/project

The optional second argument core tests the first two modules without building Fintype dependencies. The full replay builds the two required Mathlib targets and checks all sources in a fresh temporary directory. The replay prints its toolchain and Mathlib revisions and 12 axiom audits. The audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx`.
