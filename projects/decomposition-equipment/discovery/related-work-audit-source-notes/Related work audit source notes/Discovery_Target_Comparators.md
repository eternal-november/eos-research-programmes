# Open discovery target: adversarial comparator audit

**28 October 2026 — bounded primary-source audit; not a novelty clearance.**

## Finding first

Joint discovery of latent components and their dynamics/relations is established prior work, not a defensible general distinguishing claim. The closest direct challenge is mechanism-sparsity causal representation learning; factorial HMMs also infer distributed hidden causes, including their number. Valid generative parametrization can supply a genuinely learned positive joint realization. That achievement must not be dismissed merely because normalization and assembly hold by construction.

The programme remains **open**. This note compares its proposed target, not its proved results. It does not establish that any one comparator meets the whole proposed finite-state, resource-accounted, typed-interface and structural-theory package. Conversely, absence of that package in five papers is not evidence that the package is novel.

## Five comparator families

### 1. Van Gael, Teh & Ghahramani — *The Infinite Factorial Hidden Markov Model* (NeurIPS 2008)

**Supplied:** a factorial generative universe: independent binary Markov chains, transition priors, emission family; emissions must be feature-permutation invariant and ignore inactive features. **Inferred:** effective number of chains, latent trajectories, transition parameters and observation parameters—not named physical agents or a supplied decomposition of the observations. Sections 2–3 construct the Markov Indian buffet process; §3.1 and §4 give blind source separation and posterior inference using slice sampling/dynamic programming.

**Guarantee/equivalence:** a coherent Bayesian model and inference method, not a general architecture-identifiability theorem. Feature-label permutation is explicitly quotiented; posterior uncertainty is not a certified enumeration of every observationally equivalent architecture.

**Positive realization:** stochastic local transition matrices and a normalized joint emission law genuinely realize the learned model. Time dependence is retained. The latent chains are independent in the generative dynamics; dependence in the posterior after shared observations should not be mistaken for interacting physical components.

**Interfaces:** learned mixing/emissions, but no controlled action-to-port assignment, inter-chain communication constraints or distributed-controller certificate.

Primary: [paper, especially §§2–4](https://proceedings.neurips.cc/paper_files/paper/2008/file/2723d092b63885e0d7c260cc007e8b9d-Paper.pdf).

### 2. Lachapelle et al. — mechanism-sparsity causal representation learning (CLeaR 2022; nonparametric extension)

**Supplied in the published result:** latent dimension, invertible-on-image observation family with Gaussian measurement noise, conditionally independent latent coordinates given history/actions, exponential-family transitions and identifiability regularity. **Inferred jointly:** observation map, local transition mechanisms, latent temporal graph and action-to-latent graph. The latter is meaningful interface-assignment discovery; §2.5 includes unknown-target interventions.

**Theorem 5:** under Theorem 4's assumptions, one-dimensional invertible sufficient statistics, sufficient temporal/action variability and a learned graph no denser than the true graph, the graphs are recovered up to latent permutation. Its additional graphical separation criterion yields permutation-equivalent representations. Exact equality of conditional observation laws is a premise; the VAE estimator does not turn this into a universal finite-sample or global-optimization guarantee.

**Positive realization:** conditional probability mechanisms compose into a joint temporal law. Conditional independence of innovations does **not** make the latent components dynamically independent: learned cross-time edges generate persistent correlations.

**Interfaces:** unknown causal influence/support is inferred; finite communication alphabets, physical decoder placement, channel capacity and controller-capability typing are not the theorem's output.

Primary: [published paper and metadata](https://proceedings.mlr.press/v177/lachapelle22a.html), [Theorem 5 and §2.5](https://proceedings.mlr.press/v177/lachapelle22a/lachapelle22a.pdf).

**Important strengthening, separately versioned:** *Nonparametric Partial Disentanglement via Mechanism Sparsity* (arXiv:2401.04890, v2 dated 31 July 2026; do not silently attribute this version to the 2022 theorem) removes the exponential-family restriction. Assumptions 1–4 retain known latent dimension/noise variance, a diffeomorphic decoder, full-support conditional densities, no instantaneous latent effects and smoothness. Theorems 22/24 concern continuous/discrete auxiliary inputs; Theorem 32 concerns temporal dependencies. Under exact observational equivalence, sufficient influence and sparsity, they recover graph structure up to permutation and characterize remaining entanglement through **consistency equivalence**. A further graphical criterion gives complete disentanglement. Thus partial identifiability and explicit residual equivalence are already central, not omissions we can claim to introduce. [Version-pinned primary text](https://arxiv.org/html/2401.04890v2).

### 3. Lippe et al. — *Causal Representation Learning for Instantaneous and Temporal Effects in Interactive Systems* / iCITRIS (ICLR 2023)

**Supplied:** observation sequences plus per-variable intervention-target indicators; targets need not reveal latent values, observation coordinates or block dimensions. The method learns a latent-to-causal-block assignment, observation map, transition model and instantaneous causal DAG.

**Theorem 3.4 / Appendix D.2:** population likelihood optimization with universal approximators, information maximization in the residual block, graph-edge minimization and non-deterministically related intervention indicators identifies the minimal causal variables and graph in its stated sense. Assumptions include partially-perfect interventions removing instantaneous parents, common/full support, symmetry breaking, acyclicity, faithfulness and causal sufficiency. Identified blocks may be multidimensional; intervention-invariant information can remain in the residual block. This is not a finite-sample identification guarantee.

**Positive realization/correlation:** the learned conditional probabilistic model gives joint temporal dynamics, including instantaneous and delayed dependencies; it is not merely an independent fit to pre-extracted agents.

**Interfaces:** intervention labels supply more allocation information than raw action labels with unknown targets. Nevertheless, learning the observation-to-block assignment is substantial discovery. There is no bandwidth/memory-accounted distributed implementation or controller matching theorem.

Primary: [ICLR paper, Theorem 3.4 and Appendix D.2](https://arxiv.org/pdf/2206.06169); [publication metadata](https://arxiv.org/abs/2206.06169).

### 4. Li et al. — *On the Identification of Temporal Causal Representation with Instantaneous Dependence* / IDOL (ICLR 2025)

**Supplied:** an invertible nonlinear mixing model with fixed latent dimension, independent exogenous noises and temporal/instantaneous structural mechanisms. **Not supplied:** latent coordinates, observation grouping, intervention targets or the actual causal graph.

**Published Theorem 2:** smooth positive densities (A1), sufficient derivative variability (A2), empty intimate-neighbor sets in the temporal Markov network (A3), exact observational equivalence and minimum learned edge count imply Markov-network isomorphism and componentwise identification up to permutation/invertible transformations. **Theorem 3** adds unequal delayed-parent sets for adjacent instantaneous variables to obtain causal-graph identification. Otherwise causal equivalence must be respected. These are population statements, not a guarantee that finite-data variational training reaches the identifying optimum.

**Positive realization/correlation:** a learned latent generative dynamics model supports positive temporal laws with interacting components; instantaneous dependencies are explicitly allowed. No assumption of supplied named agents is needed.

**Interfaces:** graph influence is learned, but the theorem does not certify bounded physical messages, distributed availability of decoded variables, typed interfaces or controller matching.

Primary: [official proceedings](https://proceedings.iclr.cc/paper_files/paper/2025/hash/5726513facc85f802be4a25e77fb9765-Abstract-Conference.html), [published PDF, Theorems 1–3](https://proceedings.iclr.cc/paper_files/paper/2025/file/5726513facc85f802be4a25e77fb9765-Paper-Conference.pdf). This entry uses the **published** A3, not the later arXiv revision's expanded condition.

### 5. Hayden, Yuan & Gonçalves — *Network Identifiability from Intrinsic Noise* (IEEE TAC 2017)

This is the strongest checked comparator here for **alternative network realizations**, though not raw-mixture component discovery.

**Supplied:** stable globally minimal continuous-time LTI universe, directly observed manifest coordinates (`C=[I 0]`, `D=0`), unknown white-noise inputs with identity covariance; primary results assume square diagonal full-rank input DSF `P`. The actual network dynamics/topology and hidden-state realization are not given.

**Theorem 2:** adding minimum phase identifies the dynamical structure function `Q` and `P` up to input signs from output spectral density. **Theorem 3:** without minimum phase, an algebraic Riccati equation plus additional realization constraints characterizes equal-spectrum alternatives. §III-C constructs all solutions for a simpler case. These are second-order observational equivalences, not generally equality of all history laws without further distributional assumptions.

**Realization/interfaces:** real stochastic LTI realizations, not signed probability tables. DSF edges encode dynamic influence among manifest signals, potentially through latent states. The input allocation assumption is genuine supplied structure; hidden physical factorization is not uniquely recovered. Digital bandwidth, finite port alphabets, distributed decoding and controller-capability certificates are outside these results.

Primary: [author manuscript, Theorems 2–3 and §III-C](https://arxiv.org/pdf/1310.0375); [institutional publication record](https://www.repository.cam.ac.uk/items/c4a4bea7-1a44-411b-8052-2a71ff0eec0e).

## Fair comparison rules and the current acceptance-language risk

The current proposed contract was inspected at `Proposed Research Completion Contract.txt` (v0.3). No contract edit was made.

1. **A model universe is not the answer.** Fixed dimension bounds, known input alphabets, structural/causal assumptions and chosen mechanism families are legitimate for both previous work and our programme. Test whether premises supply the actual sought coordinates, allocation or factorization—not whether some inductive bias exists.
2. **Construction by parametrization counts.** Unknown decoder, factors, mechanisms and graph jointly fitted within a positive generative class are genuine inference. An independent checker may verify that construction rather than demand a second, artificially difficult assembly problem. Separately fitted components whose interfaces or dynamics cannot coexist remain valid obstruction cases.
3. **Independent innovations are not independent systems.** O2's phrase “independent noise with automatic assembly” risks rejecting ordinary coupled stochastic mechanisms by definition. Interpret the exclusion narrowly as supplying the answer or bypassing the target inference burden—not as banning a successful jointly learned construction. O1's prohibition on assumptions “making assembly automatic” needs the same distinction. This is a clarification issue, not a finding that the whole gate is wrong.
4. **Positive global compatibility is not itself novel.** A valid single generative process yields compatible overlapping marginals. If “crossing descriptions” demands more—different distributed factorizations, bounded interfaces, witness-sensitive transport—state and prove that extra requirement. Do not conflate it with ordinary marginal consistency.
5. **Alternatives are already studied.** Bayesian posterior uncertainty, causal equivalence, partial disentanglement and spectrally equivalent network realizations differ from one another. Specify which equivalence and coverage our output promises; merely retaining more than one candidate is not a new principle.

## Remaining comparison burden, not a novelty claim

The concrete first test should translate the closest joint learner into the proposed witness schema under **matched access and model assumptions**. Record what already qualifies and the exact failed obligation, rather than excluding it because its construction is generative.

- **Physical realization:** distinguish causal-influence edges from an executable allocation of local state, readouts, messages and shared randomness. Charge any central nonlinear decoder, persistent channel state and memory. Then compare to structured state-space / network realization results, not only representation learning. The DSF comparison above shows this literature already handles distinct compatible realizations; its full relationship to the proposed interface formalism remains **unclosed**.
- **Coverage and guarantees:** distinguish a single sound fitted construction, characterization of all compatible architectures, population identifiability, and finite-data uncertainty valid after model selection. None implies the others.
- **Persistent correlations:** say which correlated initializations, shared noise and coupled transitions must be represented. Do not label all independent-noise causal models inadequate: coupled transitions already create correlations.
- **Structural contribution:** demonstrate a theorem-level or measured improvement from the abstract decomposition machinery over the closest joint generative baseline—e.g. an actual additional certified decomposition, sharper justified uncertainty set or less expensive verification. A renamed causal graph or standard marginalization is insufficient.
- **Downstream control:** establish the claimed reusable type/capability judgment and its resource bound. Do not add a feature simply because these five comparators lack it; tie it to the original problem and test its utility.

**Bottom line:** genuine architecture discovery already exists in important declared universes. The plausible research question is the specific, still-unproved integration of discovery with resource-accounted compatible distributed realizations and the proposed structural guarantees. Whether that integration is new, useful, or already reducible to existing structured-realization methods is not settled by this bounded pass.
