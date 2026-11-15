# Lax synchronization with retained interfaces

A conditional general construction for synchronizing native transition squares through lax limits, while retaining state and interface agreement cells.

## Result

For strict 2-functors P,Q from a state/interface 2-category to a transition 2-category, the native colax-dialgebra doctrine creates selected lax limits whenever Q preserves them. No preservation assumption on P and no invertibility of native comparison cells is required. Projections are strict and jointly detect strictness.

The changing-interface application takes state, input and output together. Joint cartesian product preserves these limits; product with a fixed output need not. The relative application retains pure-map tags even when J is nonfaithful. Its terminal-state sector recovers the specified relative-quintet square data.

## Read

- [Theorem, proof and hypotheses](Lax_Dialgebra_Synchronization.tex)
- [Source integrity manifest](MANIFEST.json)
- [Native state flattening](../native-state-flattening/README.md)

## Scope and literature

The construction uses established lax-limit and enhanced-algebra machinery, with an explicit recovery of the unary-monad case of Lack–Shulman. No novelty claim is made.

This is not automatic for arbitrary ordinary state categories, pure interfaces or output actions. The theorem assumes an actual strict 2-categorical presentation, not an unproved strictification. Compatibility with retained-state feedback and flattening is a further obligation; this does not complete general concurrency or instantaneous feedback.

## Verification

Independent written-proof review; source and manifest checks only. No executable semantic test, Lean certification, TeX compilation or CI proof is claimed.
