# Candidate-specific scope and prior-art audit

28 October 2026. Inspected `main/Partial_Subsystem_Discovery.md`, `exterior/Exterior_Closure_and_Feedback.md`, and `stress/Unobserved_Exterior_Family.md`. This is an independent scope/prior-art assessment, not formal verification or an exhaustive priority search.

## Plain-language verdict

This is genuine discovery, but discovery of a particular kind: the method learns which distinctions in a noisy local sensor patch form a task-preserving state model, and which incoming signals and their history it needs. The whole environment is neither supplied nor reconstructed. That is meaningful progress on the newly approved local-discovery objective.

It is not yet discovery of a physical modular architecture. The output is a stochastic quotient of a latent patch state. The remainder can still inspect the retained system's private state. A probability-law factorization preserves correlations, but does not show that the discovered part is a physically separable device or that its outgoing communication obeys a restricted interface. The substantial typed-decomposition machinery is not essential to the present proof. Do not imply otherwise.

Recommended milestone label: **readout-based discovery of an exterior-robust task quotient**. Treat it as an intermediate result, not completion of the broader architecture-discovery programme.

## What is actually inferred

- The finite patch alphabet and noisy sensor calibration, under a supplied grouping of three independent informative views.
- A task-preserving quotient not supplied in advance, using iterative response-based refinement and hidden-effect tests.
- A sparse input-history context and a recursively updated deterministic boundary quotient.
- A finite obstruction when no admissible deterministic task quotient exists in this declared patch-state universe.

Thus this is not verification of an already supplied controller against an already supplied model. Nor is it merely extraction from a supplied whole-state transition table. However, the candidate sensor patch, task readout, input-channel bank, memory/width bounds and intervention grammar are supplied. Discovery is constrained by them.

## Strong assumptions doing identification work

The randomized post-history probe must have no direct local effect and must shift the binary hidden influence in the same direction by at least delta at every relevant full history. All other omitted effects on the patch must factor through that mode and the unknown bounded input context. This is a strong causal promise. It is not diagnosed by observing invariance, and it is not free experimental access contained in arbitrary passive readouts.

The unknown mode probabilities do not have to be estimated: randomization plus the sign/uniform-gap promise forces every nonzero hidden response contrast to appear in an observed regime contrast at the true context. This is the key extra identification ingredient beyond ordinary controlled minimization. It prevents cancellation without revealing the quotient labels. The promise is narrower than arbitrary hidden surrounding dynamics, although the surrounding state and memory may be arbitrarily large.

Pair-union context coverage is necessary for the stated arbitrary-input-policy conclusion. Separate coverage of each candidate context cannot rule out substituting a spuriously correlated channel. The revised main note correctly requires coverage up to 2k slots. Where physics forbids Cartesian support, the broad policy claim must be restricted rather than retained unchanged.

## Closest comparison: invariant causal prediction

Peters, Bühlmann and Meinshausen, *Causal inference using invariant prediction: identification and confidence intervals*, JRSS B 78(5) (2016), 947–1012. Primary manuscript: https://arxiv.org/pdf/1501.01332 . Published page: https://academic.oup.com/jrsssb/article/78/5/947/7040653 .

Theorem 1 controls false positive causal selections using valid tests of invariant prediction; Theorem 2 gives identification under specified sufficiently informative interventions in linear structural-equation settings. The principal setting supplies observed predictors and target and excludes hidden confounders affecting the target, with extensions discussed. Its intervention locations need not be known. Hence invariance across unknown interventions and environment-robust predictor selection are established mechanisms. Our candidate instead learns a quotient of a noisy latent patch and interleaves hidden-effect exclusion with controlled state refinement. That integrated distinction should be stated narrowly, not as a new invariance principle. A strong experiment-richness assumption remains central in both.

## Closest comparison: controlled state minimization

Givan, Dean and Greig, *Equivalence notions and model minimization in Markov decision processes*, Artificial Intelligence 147 (2003), 163–223. DOI 10.1016/S0004-3702(02)00376-4. Primary full paper: https://ics.uci.edu/~dechter/courses/ics-295/fall-2019/papers/givan-dean-greig.pdf .

Theorem 7 establishes preservation under stochastic-bisimulation quotients; the partition-iteration development constructs stable state equivalences from transition and output/reward behavior. This is the direct baseline for the main refinement proof, not a remote analogy. Here the transition rows used in refinement must first be recovered and certified insensitive to unresolved exterior effects; the old whole patch need not itself have autonomous Markov dynamics. That is a real access-and-identification difference, but the coarsest-quotient argument is standard. Recursively minimizing an input-history register is likewise finite-state transducer minimization, not a new mechanism.

## Influence abstraction and local identification

For details and inspected assumptions see `Prior_Art_and_Target_Fidelity.md`. Standalone primary links:

- Oliehoek, Witwicki and Kaelbling, JAIR 70 (2021), 789–870, Theorem 1: https://arxiv.org/html/1907.09278 . Exact local predictions with exterior factors eliminated, starting from a known model and chosen local factors.
- Ramaswamy and Van den Hof, IEEE TAC 66(11) (2021), 5237–5252, Theorems 1–2: https://pure.tue.nl/ws/files/191722736/A_Local_Direct_Method_for_Module_Identification_in_Dynamic_Networks_With_Correlated_Noise.pdf . Local module identification with unmeasured nodes/correlated noise, using known topology and selected target.
- He, Suau and Oliehoek, NeurIPS 2020: https://papers.nips.cc/paper/2020/file/2e6d9c6052e99fcdfa61d9b9da273ca2-Paper.pdf . Learned incoming influence using a supplied factored global simulator.

These rule out broad novelty claims based only on leaving the exterior unknown or learning an incoming influence model.

## Decomposition content and remaining gap

The map X -> (s, residual in the fiber over s) is a dependent-state representation. Conditional disintegration then generates the original joint law from the quotient draw followed by a remainder draw. This is correct standard probability structure. Because the remainder may inspect full old X and receive full new s, it does not establish independent components, a small outward boundary, or safe substitution under an unchanged physical communication contract.

The joint-quotient obstruction is useful: individually invariant marginals may retain exterior-dependent correlation. It correctly prevents treating separate predictive successes as a joint module. Its proof is elementary; it does not itself derive a general coherent reconstruction theorem using virtual-equipment operations.

A stronger subsequent architectural result would have to discover both incoming and outgoing sufficient interfaces, with each message generated from its permitted sender history, and prove that simultaneously discovered parts admit one positive implementation under that communication grammar. This is a statement of the remaining gap, not a request to replace the current milestone with another small exercise.

## Reporting recommendations

1. Lead with what the algorithm discovers, then explicitly call it a quotient rather than a physical partition.
2. Say that the exterior is unobserved, not that the result works without restrictions on its possible local effects.
3. Say intervention-tagged readouts are required. Do not call this a stronger theorem on the same passive data as earlier milestones.
4. Separate the directly accessible-port theorem from the noisy latent-port stress example; the latter establishes a generative interface, not exact runtime decoding.
5. Do not count full-equipment, bidirectional architecture discovery, physical controller suitability, or the original contract as discharged.
6. Credit the standard mechanisms. The warranted contribution claim is a bounded integration and identification result; neither substantial novelty nor triviality follows from this scoped audit alone.
