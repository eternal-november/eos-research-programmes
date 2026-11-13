# Reusable predictive interface discovery: coverage and nearest-baseline audit

29 October 2026. Internal research audit, not a novelty clearance. Primary web sources were inspected on this date; earlier exact source comparisons are identified separately below.

## Plain-language abstract

Predicting an environment from its observation history is not a new goal. Neither is compressing that history into a state that updates after each new observation. The additional problem worth solving here is discovering *several locally maintainable states and their interfaces* when observations do not determine a unique underlying system. The proposed parts must describe one possible joint process, preserve correlations through time, and remain usable when the controller changes within an explicitly supported family. A collection of individually accurate predictors does not guarantee this. Earlier project results already cover much of the algebra and some tightly structured identification examples. The new milestone should earn its value through an actual discovery construction that closes these gaps, not through restating recursive sufficiency or adding controller quantifiers to a known predictor.

## 1. Exact internal boundary

### What is already established

* `persistent_interface_discovery_20261028/Constructive_Target.md`, sections 3, 9.3–9.5: local positive kernels, causally maintainable persistent interfaces, charged initialization/sampling and all finite joint readout laws, in a hidden-correlation path class. Section 9 constructs heterogeneous parameters from local moments and gives finite-horizon TV stability. The broader coupled family recovers a canonical mixing partition under a strong algebraic identification regime. Therefore recurrence, positive assembly and finite-horizon transfer are not individually new targets.
* `ambiguous_decomposition_discovery_20261028/Prior_Lifting_Boundary.md`: the preceding project already had finite unknown-chart completion, all-history fixed-world reconstruction, hardware-aware semantic discovery, and constructive crossing recognition. The ambiguous-discovery milestone adds learned calibration/source marginals while retaining unresolved positive source processes. Merely keeping a set of models is not an advance over that baseline.
* `local_mechanism_discovery_20261028/main/Dynamic_Product_Atlas_Discovery.md` and `gluing/Positive_Atlas_Gluing.md`: noisy patch calibration, local coordinate and parent discovery, conditional-patch positive gluing, controlled recursive quotienting and finite-data qualifications. The audit explicitly distinguishes identifiable latent labels from an executable online state estimator. This distinction remains central: knowing a latent mechanism's law does not grant a robot access to its instantaneous state.
* `certificate_guided_discovery_20261029`: unknown bounded scopes, update maps, ownership and encoders, checked by local update/output identities; pathwise transfer under arbitrary action/source sequences. But a finite table/model universe and supplied semantic supports do considerable work; finite data establishes possible-world consistency rather than unrestricted discovery.
* `safety_representation_discovery_20261029`: executable scheduled observers and unknown report synthesis over causal evidence laws. Its successful state is a representation sufficient for a selected risk certificate, not a reusable predictor of future environment response. This is the clearest immediate gap.
* `related_work_audit_20261028/Positive_Realization_Audit.md`, sections 1–3: finite Hankel reconstruction and adaptive-controller finite-horizon TV already proved for valid controlled laws; positive channel-factor/retraction certificates already proved in a fixed frame. Low rank alone is explicitly insufficient for a finite positive implementation.

### What would count as additional

Derive locally executable predictive state/interfaces from incomplete observation laws while preserving unresolved global couplings, *without* supplying the sought scopes or secretly decoding the whole latent state. Demonstrate a discovery or representation advantage beyond exhaustive finite completion. Establish joint recursive closure and controller-family prediction for the same implementation, not unrelated per-controller fitted models. If the result is instead a sound bounded certificate calculus, describe that honestly and demonstrate its actual extra expressive or algorithmic power.

## 2. Closest external baselines, not a field catalogue

### Factored predictive state representations

Wolfe, James and Singh, *Approximate Predictive State Representations* (AAMAS 2008), section 4, Theorems 5 and 7: factor scopes trade compactness against predictive information; models can be learned without a monolithic predictor. Their approximate joint prediction and conditional-independence conditions are the comparison to make. Local PSRs and scope growth are not new mechanisms. Additional obligations here are one positive persistent joint realization, implementable information flow and ambiguity-aware evidence certificates.
https://www.ifaamas.org/Proceedings/aamas2008/proceedings/pdf/paper/AAMAS08_0647.pdf

### Controlled causal states

Barnett and Crutchfield, *Computational Mechanics of Input–Output Processes* (2015/2016 manuscript), sections VI–IX: causal equivalence of input/output histories gives an optimal predictive transducer, with recursive state dynamics. This is the nearest baseline for a proposed equivalence based on all permitted future experiments. It does not alone discover a decentralized boundary architecture from incomplete data. Nor does its existence imply a finite state set, a finite synchronization time, or access to the necessary history at every local owner.
https://csc.ucdavis.edu/~cmg/papers/et1.pdf

### Learned predictive coordinates

Littman, Sutton and Singh, *Predictive Representations of State* (2001), establishes the predictive alternative to hidden-state descriptions. Boots, Siddiqi and Gordon, *Closing the Learning–Planning Loop with Predictive State Representations*, supplies statistically consistent spectral learning and planning. Their prediction-coordinate mechanism must be credited if used. The gap is not simply avoiding latent-state recovery; it is deriving legal local positive implementations and retaining joint uncertainty.
https://papers.nips.cc/paper_files/paper/2001/hash/1e4d36177d71bbb3558e43af9577d70e-Abstract.html
https://arxiv.org/abs/0912.2385

### OOM and positive realization

Thon and Jaeger (2015) relate multiplicity automata, OOMs and PSRs. Finite linear predictive dimension does not force a same-sized finite stochastic hidden realization. The project's earlier positive-realization audit already checked Anderson's invariant-cone baseline and its local-channel limitations. Thus a new local cone certificate is not itself a new positive-realization principle; its discovery, locality and coupling claims need their own proofs.
https://jmlr.org/papers/v16/thon15a.html
https://doi.org/10.1007/PL00009846

### Decentralized information states

Nayyar, Mahajan and Teneketzis, *Decentralized Stochastic Control with Partial History Sharing* (2013), reformulate control through common information and prescriptions applied to private information. This is directly relevant when a proposed interface carries shared belief or common memory. Their supplied information structure does not solve unknown interface discovery. Conversely, calling a global common-information belief an executable local state is unjustified unless its construction, communication and storage are actually supplied.
https://arxiv.org/abs/1209.1695

### Reusable causal abstractions

Wang et al., *Building Minimal and Reusable Causal State Abstractions for Reinforcement Learning* (AAAI 2024), is a direct reuse baseline, not a distant analogy. Its factored-state assumptions differ from partial-readout local-state discovery. Reuse itself is not new; our claim must concern the source of the representation, unresolved couplings and its executable decomposition.
https://arxiv.org/html/2401.12497v1

The earlier local-mechanism audit additionally contains exact comparisons to FactoRL, Bayesian factored POMDP learning, active learning of sound negotiations and multiview causal discovery. Those are retained baselines rather than omitted competing work.

## 3. Non-negotiable pitfalls and tests

1. **Marginal predictive sufficiency is not joint sufficiency.** Let B be a fair persistent bit, R_t independent fair bits, and outputs X_t=R_t, Y_t=R_t XOR B. Each output process alone is iid fair and needs no predictive memory. Joint observations reveal B; future joint parity must preserve it. Two zero-memory marginal predictors resampling their coupling each tick get the joint process wrong. A legal realization must retain the shared bit or equivalent state. Its location, initialization and access cannot be free.
2. **Finite data cannot certify infinite-history equality without a promise.** A process agreeing through the observed/tested horizon may differ later. Declare bounded memory/rank, synchronization, approximation or a finite-horizon target. Do not call a finite empirical suffix test universal predictive equivalence.
3. **Belief recursion is not finite memory.** Finite hidden states can require continuously many belief values. An algebraically recursive update with real-valued state is not a finite-bit implementation without precision/error analysis. Distinguish alphabet size, arithmetic dimension, bit storage and sample complexity.
4. **Equal local forecasts do not license independent innovations.** Overlapping parts can share noise or hidden persistent parameters. Positive one-step patch kernels require a common joint extension and temporally consistent initialization; pointwise feasibility may switch hidden worlds between ticks.
5. **A controller family needs causal support.** A behavior policy that never invokes an action cannot determine its response without a model promise. Equality under one closed-loop policy is weaker than controlled-law equality. Off-policy interventions require exogeneity and coverage; an evidence gap is not repaired by creating a larger observer.
6. **Unknown boundaries must be outputs.** Supplied sensor ownership is a legitimate resource contract, but supplying the desired causal partition, independent innovation groups, or a separating reset should not be relabeled discovery. Explain which scopes remain unknown and why their recovery is not graph connectivity in disguise.
7. **Separate single implementation from per-world fitting.** The causal update/communication program must be common when runtime cannot identify the world. World-specific proof witnesses may differ. A result of the form every world has some implementation does not produce one reusable installed interface.
8. **Avoid global-state computation in a local theorem.** Charge joint-history tables, exact filtering, normalization, conditional-independence oracles, tensor contractions and graph width. A bounded local state count is not a polynomial algorithm if finding or checking it invokes an exponentially sized whole law.
9. **Calibration and usefulness remain separate.** The predictor may be useful for observable tasks while physical hazards need an additional sound hazard relation. Predictive decomposition is not a physical architecture identification claim.

## 4. Recommended acceptance boundary

A substantive positive target should have an explicit input/evidence regime, a nontrivial family with hidden boundaries and persistent coupling, an executable discovery algorithm, coherent positive joint witness family, and a declared controller-class theorem with quantitative coverage and error. At least one decisive obligation should be derived rather than assumed: joint recurrence, legal local accessibility, or discovery of missing interaction scope. A general certificate theorem plus an honest substantial class can satisfy this; no need to invent an entirely new mathematical mechanism. A bare causal-state quotient, exhaustive model enumeration, or a new impossibility example cannot by itself satisfy the approved target.
