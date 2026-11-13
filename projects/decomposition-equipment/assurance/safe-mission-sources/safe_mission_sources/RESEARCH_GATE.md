# Safe mission completion: target gate

Authorized 29 October 2026. This is mathematical and simulation research, not hardware deployment.

## Central question

Can a robot safely acquire a useful decomposition of an initially uncertain environment and use its discovered interfaces and memory to complete new missions, without first learning or planning over the entire joint environment?

## Required distinctions

- Safety alone is insufficient: a controller that always refuses to move fails the mission.
- Completion alone is insufficient: safe acquisition, initialization, preparatory actions, traversals, fallback and terminal behavior all belong to the execution.
- A supplied model class is legitimate; supplied actual scopes, memory, factor graph or hidden mode are not discovery.
- The learner may use only its declared observations and actions. Simulator truth is confined to generation and independent scoring.
- Finite data do not certify absence of arbitrary rare hazards. State the structural support/calibration premise and confidence event separately.
- Persistent environmental uncertainty must not silently become an adversary that changes model at each step. A conservative rectangular relaxation is allowed only when labeled and its lost completeness is measured.
- Safe probing requires an explicit justified initial envelope, not a free oracle or unexplained reset. Distinguish information that can safely be obtained from information that would require violating the safety obligation.
- A decomposition result must do work beyond ordinary global belief-state planning. Charge discovery, witness, storage, communication, evidence and synthesis costs separately.

## Outcome and comparison

Target useful task completion under a common safety requirement, including deadline/energy where justified. Use a serious conservative baseline, a fixed-decomposition baseline with the same information and valid cross-block handling, and a supplied-structure or joint-model reference where feasible. Do not claim superiority to an oracle; recovery of oracle capabilities without supplied structure can be meaningful. Report failed or inconclusive comparisons.

Hold out mission combinations, not merely random replay seeds. Reuse must preserve the interface and applicability contract, rather than extrapolate to unsupported physical interventions.

## Stop or redirect before implementation

Reject a target whose discovery can be replaced by one obvious scalar threshold, whose task is a chain of independently solved identical stops, or whose entire difficulty is supplied in a global candidate table. Small counterexamples remain valuable tests but are not the motivating result.

## Deliverable

A precise conditional construction with proof, a substantive executable family, safe-indistinguishability obstruction where applicable, reproducible tests and meaningful baselines, an independent challenge, and a plain-language abstract. Honest limitations are part of the result. No literature-wide novelty or full original-contract discharge is presumed.
