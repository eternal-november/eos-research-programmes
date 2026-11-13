# Partial-subsystem discovery: baseline and target-fidelity audit

Status: preliminary primary-source audit, 28 October 2026. This is not a priority judgment. The candidate theorem must still be checked against these obligations.

## Plain-language conclusion

Learning about one part of a network without modeling everything else is an established objective. The substantive target here is harder: from noisy readouts, discover what the local parts and their boundary actually are, while allowing unresolved surroundings. A theorem that assumes the correct local state and sufficient boundary in advance would miss that target.

## Closest primary baselines

### 1. Influence-based abstraction: exact local behavior without exterior state

Oliehoek, Witwicki and Kaelbling, *A Sufficient Statistic for Influence in Structured Multiagent Environments*, JAIR 70 (2021), 789–870. https://arxiv.org/html/1907.09278

Theorem 1 proves finite-horizon best-response equivalence between the global model and its influence-augmented local model. Its proof preserves local transition, observation and reward predictions. This includes within-stage dependencies. The construction summarizes exterior influence using conditional distributions given suitable local histories. The model/DBN is explicitly assumed known; local state factors and influence sources are specified before abstraction. History summaries need not have uniformly bounded finite cardinality. This builds on the authors’ AAAI 2012 work.

Audit consequence: neither removing exterior latent factors nor replacing them with a sufficient incoming process is novel by itself. Our possible advance must be identification of the local factors and interface from readouts, with an explicit model-relative completeness or ambiguity statement and implementability accounting.

### 2. Local-module identification: unmeasured nodes and confounding

Ramaswamy and Van den Hof, *A Local Direct Method for Module Identification in Dynamic Networks With Correlated Noise*, IEEE TAC 66(11) (2021), 5237–5252. DOI 10.1109/TAC.2020.3035634. https://pure.tue.nl/ws/files/191722736/A_Local_Direct_Method_for_Module_Identification_in_Dynamic_Networks_With_Correlated_Noise.pdf

Linear scalar-node dynamics, network topology, target link and Boolean disturbance-correlation pattern are supplied. Theorem 1 gives module invariance under eliminating unmeasured signals and removing confounding effects, with path/loop and confounding conditions. Theorem 2 establishes prediction-error consistency under correct model-set membership, data informativity and delay conditions. Algorithms choose measured inputs and outputs; they need not identify the entire network. Thus conditional identifiability with a partly unmeasured surroundings is already substantial established theory. Discovering hidden local coordinate systems and recurrent boundaries is a different burden, not something this paper claims.

Earlier direct baseline: Dankers et al., *Identification of dynamic models in complex networks with Prediction Error Methods: Predictor Input Selection*, IEEE TAC 61(4) (2016), 937–952, DOI 10.1109/TAC.2015.2450895. https://repository.tudelft.nl/record/uuid%3A05358668-5a0b-44ed-87b4-a136ef0434b9 . Known interconnection structure and chosen target module precede predictor-input selection. The paper gives sufficient consistency conditions, rather than unknown architecture discovery.

### 3. Latent local causal discovery

Gao and Ji, *Constrained Local Latent Variable Discovery*, IJCAI 2016, 1497–1503. https://www.ijcai.org/Proceedings/16/Papers/214.pdf

The method searches latent variables within the Markov blanket of a supplied target variable. It exploits blanket topology and constrained structural expectation-maximization, with empirical evaluation. This is relevant proof of an existing research objective, but the inspected paper does not offer a general identifiability/completeness theorem for arbitrary latent blankets. Do not use it as such. Conversely, merely learning latent factors near a supplied target is not a new research problem.

### 4. Predictive states and local predictive scopes

Littman, Sutton and Singh, *Predictive Representations of State*, NeurIPS 2001. https://proceedings.neurips.cc/paper/2001/file/1e4d36177d71bbb3558e43af9577d70e-Paper.pdf . A controlled process can be represented by action-conditional future-test probabilities; finite POMDP size bounds the dimension of an available linear predictive representation. This does not provide positive local physical mechanisms or unsupplied architecture.

Shalizi and Crutchfield, *Computational Mechanics: Pattern and Prediction, Structure and Simplicity*, Journal of Statistical Physics 104 (2001), 817–879. https://arxiv.org/abs/cond-mat/9907176 . Causal states identify histories with the same predictive future law and yield a minimal predictive representation. Such an equivalence relation alone is not a finite-state discovery algorithm or a physical subsystem decomposition.

Wolfe, James and Singh, *Approximate Predictive State Representations*, AAMAS 2008. https://www.ifaamas.org/Proceedings/aamas2008/proceedings/pdf/paper/AAMAS08_0647.pdf . See the preceding milestone’s audit for inspected Theorems 5 and 7 on predictive scope/rank and KL improvement. Avoiding a whole predictive model is not sufficient distinction; positive coupled realization and operational boundaries remain additional obligations.

## Acceptance tests for the new theorem

1. Input must be readout laws/samples and declared structural bounds, not a whole-state kernel, true factor set, parent graph or sufficient separator.
2. Discovered local factors may be named only up to justified coordinate gauge; distinguish physical recovery from an observable realization class.
3. Exterior factors must genuinely remain uncovered. Relabeling a fully covered atlas or aggregating already reconstructed factors does not remove the old coverage assumption.
4. A bounded local Markov order is a strong model promise. Checking conditional independence for one finite past cannot certify all-history sufficiency outside that promise. Hidden surroundings can carry arbitrarily delayed information.
5. Passive readout equality need not imply intervention equality. Controlled claims require action coverage and a causal sampling/invariance assumption; conditioning on endogenous action is insufficient.
6. A boundary that is an arbitrary vector of posterior probabilities can require continuous memory. If the intended output is a finite stochastic implementation, prove finite positive realization, not just finite linear predictive rank.
7. A learned latent state is not an instantaneous observation. If its use requires a decoder/filter, give its legal inputs and storage, or explicitly leave execution-level access unproved.
8. Separate local fits need not have a joint process. Require a common positive realization or a correct obstruction; observational overlap alone may miss shared randomness or hidden memory coupling.
9. An exterior-robust theorem must quantify the exterior class and how local histories/interventions change its influence. A model-correctness certificate is not a model-class-membership certificate.
10. State scaling in observable scope, local alphabet, retained memory and certificate size. Bounded widths are substantive assumptions. Do not hide a global-state enumeration in the checker.

## Useful stress tests (original audit suggestions)

- A hidden two-state source with long-lived persistence drives two measured regions. Each region alone has a compact predictor; their joint law depends on whether they share that source or use independent copies.
- Two whole models agree on the entire permitted passive observation law but react differently to an allowed action. The theorem must retain both or explicitly invoke an intervention-identifying promise.
- A family of hidden shift registers delays an influence beyond every tested window. Without a memory bound, no fixed-window acceptance test proves closure.
- A proposed boundary is predictively sufficient but is not generated by the permitted sender’s history. Reject it as a physical interface even if its centralized predictor is correct.

These are challenges to scope, not counterexamples to a theorem whose hypotheses correctly exclude them.

### Additional direct baseline: learned exterior influence

He, Suau and Oliehoek, *Influence-Augmented Online Planning for Complex Environments*, NeurIPS 2020. https://papers.nips.cc/paper/2020/file/2e6d9c6052e99fcdfa61d9b9da273ca2-Paper.pdf . The method learns an incoming-influence predictor and replaces a global simulator with a cheaper local simulator. The inspected setup starts from a factored global simulator and collects influence-training data from it; its Section 2.3 specifies local/nonlocal factors from the given global model. Thus learning the exterior influence is also established. The distinction cannot be 'we learn the influence instead of supplying it'; it must include readout-only discovery of unsupplied local mechanisms and boundary, under explicit identification conditions.

## Exact finite-window warning (independent elementary derivation)

For any tested window length k, compare fair iid bits with a stationary binary order-k process satisfying P(O[t+1]=O[t-k+1] | O[t-k+1:t])=1/2+delta, 0<delta<1/2. Its k-bit shift-register chain has uniform stationary distribution: each target k-word has two predecessor words, and their transition probabilities sum to one. Consequently every observed window of length at most k is uniformly distributed, exactly as in the iid process. Their length-(k+1) laws differ. All conditional next-bit probabilities are strictly positive.

Thus even exact bounded-window population data cannot rule out a longer-memory exterior, without a structural memory bound or other all-history identification hypothesis. An additional fixed noisy sensor channel preserves the short-window equality. This is an illustration of information insufficiency, not a novel theorem claim.
