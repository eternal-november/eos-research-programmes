# Local mechanism discovery target

Authorized by Sean on 2026-10-28 at 22:06:46 UTC, following the proposal to discover local mechanisms and interfaces from readout histories.

## Input and unknowns

Input is an explicitly stated observation protocol, finite noisy readouts and recorded actions where available. Resource bounds and a mathematical model universe are permitted. Hidden component state spaces, the correspondence between components and observed channels, wiring and boundary signals are not supplied. Physical ontology need not be uniquely identified.

## Obligations for this milestone

1. Give a constructive discovery result for positive local mechanisms, including local state and interfaces, in a growing nonlinear interacting family.
2. State exactly which quantities, equivalence classes or families of decompositions are identifiable. Retain alternatives rather than selecting arbitrary hidden labels as truth.
3. Supply actual joint realization witnesses and a meaningful crossing or refinement comparison, not just separate local fit.
4. Avoid construction or enumeration of the exponentially large whole-state model on the demonstrated growing family. Separate data, arithmetic, search, certificate and representation costs.
5. Explain statistical assumptions and margins. Do not certify membership of an arbitrary physical environment in the declared family from a finite list of moments.
6. Charge local memory, shared memory, time alignment, sensor access, message timing, preprocessing and shared random sources. A memory lower bound must survive or explicitly exclude relocation into another permitted resource.

## Main failure modes

- Unknown bounded sensor mixing was already studied. Repeating that is not the target.
- Learning a known one-state-per-port graph is not discovery of unsupplied component states.
- Pure multi-view latent-variable recovery is a baseline, not by itself the claimed decomposition result.
- Learning an entire global HMM then factoring its transition table does not meet the growing-family scalability objective.
- Trivial enumeration of every bounded candidate plus behavioral checking is not the main theorem.
- Supplied observation patches must not silently be the requested components.
- Low predictive rank does not establish positive local realization.
- Pairwise-compatible local models need not jointly realize; a common refinement cannot simply be assumed.
- Uniqueness up to renaming alone misses split/merge, hidden-memory, interface-storage and observational ambiguities.
- Known product-generative learner output is credited as a positive realization, not relabeled as a gap.

## Baselines requiring explicit comparison

Predictive state discovery; factorial and coupled hidden Markov models; FactoRL latent factored-state discovery under rich observations; multiview/tensor latent-variable identification; stochastic network identification; finite-state realization and minimization; transportation/marginal polytopes and graphical gluing.

## Status

Initial status at authorization: the theorem was open. The final report and reviewed proof notes now establish the bounded milestone under their explicit model and observation assumptions. No new original-contract clause is discharged automatically.
