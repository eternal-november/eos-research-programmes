# Independent causal uncertainty preflight

29 October 2026. These checks precede review of the main theorem candidate.

## Evidence cannot be manufactured by an observer

A newly executable joint observer does not supply its law. If archived records retain only unaligned marginal patches, the new joint statistic must remain unconstrained until it is measured or is identified by proved assumptions. For two bits with fair marginals, laws supported on 00 and 11 and laws supported on 01 and 10 have identical local observations but opposite disagreement risk. Compiling an XOR observer does not distinguish these laws retrospectively.

If the observer is chosen after looking at the same aligned records used for its confidence interval, coverage must hold simultaneously over every eligible choice, or the interval must use independent held-out records. Counting only the final selected observer in a union bound is invalid. For n=2 samples of a fair Bernoulli coordinate, its empirical support interval [min,max] has coverage 1/2 for p=1/2. For two independent coordinates, selecting a coordinate with a constant observed sample whenever available makes coverage 1/4. This is a deliberately elementary exact selection counterexample, not the proposed confidence procedure.

## Causal action constraints and policy change

Fix finite horizon and an exploration policy e(a|h) whose randomization is independent of the environment conditional on its permitted past h. A common, policy-invariant environmental kernel, arbitrary non-Markov history dependence and persistent hidden modes are allowed. For a target policy pi with support contained in e, the path likelihood ratio is the product of pi(a|h)/e(a|h). The target expectation of any bounded path function equals its e-expectation weighted by that ratio. This statement follows by cancellation of action factors in the chronological joint factorization, not by matching aggregate action frequencies.

When the optimization law includes hidden or physical prefixes, the linear causal constraints must express P(prefix,a)=e(a|h(prefix))*P(prefix) at every relevant prefix. Merely requiring the right aggregate action probability does not establish policy change. Counterexample: hidden Z is fair, logger takes A=Z, and Y=1[A=Z]. Its action marginal is fair and observed Y is always one. A fixed target A=0 has true E[Y]=1/2, whereas falsely treating the logger as randomized gives importance-weighted value one. Positivity at the observed marginal level is insufficient.

For statistical data, independent episodes permit ordinary bounded-observation confidence bounds despite within-episode dependence. One long dependent trajectory needs its own mixing, martingale or dependence argument. Data collected under a different controller or deployment condition need a justified policy-change or shift relation. The word exploration is not a substitute for that relation.

## Hazard semantics

A physical hazard certificate needs either an observed hazard variable with valid calibration or an independently justified upper decoder: actual hazard implies the decoded hazardous event, with any approximation failure budget charged. A law of readouts alone does not constrain an independent unseen hazard variable. If two admitted environments have identical readouts but one always violates the physical safety property, robust assurance must fail or explicitly assume it away.

A finite-horizon bound is not an infinite-horizon guarantee. A risk upper bound conditional on the confidence event and a confidence level for that event are different quantities. Their combination must state which probability is over data and which is over deployment.

## Persistent uncertainty must remain shared

One global law or mechanism is chosen for all steps and all certificate pieces. Replacing a shared parameter by a fresh adversarial choice at each step changes the model family. If Y_0=Y_1=Theta for one fixed unknown bit, disagreement risk is zero. A rectangular relaxation allowing the first step to choose zero and the second to choose one admits risk one. Such an upper bound may be sound but destroys exactness and can obscure which interaction was lost.

Conversely, locally optimal lower-risk realizations cannot be glued if they use inconsistent hidden parameters. Any claimed exact robust upper/lower risk comparison must retain common-law constraints, including shared source values and the controller's accessible history.

## Dual and diagnostic scope

Finite-dimensional LP duality is available for a nonempty bounded primal confidence polytope; infeasible data constraints require a separate inconsistency result, not an arbitrary safety value. Every dual coefficient and risk decoder must be well typed on the trace information it uses. A dual potential on inaccessible joint values is a mathematical certificate but not yet an executable observer.

Different failures need different witnesses. A large upper risk may arise from a truly dangerous compatible environment, unresolved evidence, an intentionally coarsened representation, or an unavailable message. A risk-separating pair of laws diagnoses uncertainty only if both belong to the stated evidence set. A relaxed-model adversary excluded by retained full evidence instead diagnoses loss due to representation. A factorization counterexample to an encoder diagnoses implementation. These are not interchangeable.

## Statistical ambiguity is not structural indistinguishability

Two laws in the same finite confidence region may predict different population measurement laws. Their risk separation proves that the current evidence does not certify the decision, but more observations of the existing variables may resolve it. A claim that a NEW interaction must be measured needs the stronger witness: identical population information for every currently admitted observer, with different task risk. Equality only of selected moments establishes necessity relative to those moments, not relative to every statistic of the original readout logs.

Likewise, an adversarial law admitted after dropping evidence constraints but excluded by the full current evidence diagnoses representation loss; it is not an actual remaining physical possibility under that evidence set. Report these cases separately.

## Countable observer programs and simultaneous coverage

A fixed finite observer catalogue is not required for the coverage argument. Assign weights w_O>0 summing to at most one to a countable family of observer programs (for example through a prefix code). If a bounded statistic from each observer is computed on n_O independently sampled episodes with the requisite aligned inputs, apply a failure allocation delta*w_O and Hoeffding radius sqrt(log(2/(delta*w_O))/(2*n_O)). A countable union bound yields simultaneous validity, hence validity for any subsequently chosen finite subset of programs. This is only a coverage construction, not efficient program synthesis or a way to reconstruct missing input streams. If sample inclusion or n_O is selected based on outcomes, a separate selection-safe confidence argument is required.
