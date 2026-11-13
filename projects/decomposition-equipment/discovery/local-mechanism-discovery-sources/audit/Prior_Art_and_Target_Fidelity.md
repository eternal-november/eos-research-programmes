# Prior art and target fidelity for local mechanism discovery

Status: baseline audit initiated on 28 October 2026 and retained with the completed bounded milestone. This note records the target and prior-art obligations; the subsequent candidate review and independent mathematical review are in Candidate_Proof_Review.md and ../Review_Dynamic_Discovery.md. It is not a scientific-priority verdict. Primary references below were inspected at the indicated result level. No inference of novelty follows from an unsuccessful search.

## Strongest immediately relevant baselines

### FactoRL already discovers a latent factorization without joint-state enumeration

Misra, Qinghua Liu, Jin and Langford, *Provable Rich Observation Reinforcement Learning with Combinatorial Latent States*, ICLR 2021. Primary paper: https://openreview.net/references/pdf?id=0wpcsuBLCN

Definition 2 supplies binary latent factors but leaves the partition of observation atoms among factors unknown. Emission supports for alternative factor values are disjoint, so a current observation determines the hidden state. Dynamics are nonlinear factored transition tables with bounded parent sets. Assumptions 1–3 require backward-dynamics separation, persistent within-factor atom dependence, and realizable regression classes. Interaction uses episodic exploration from a deterministic start, with regression and planning oracles.

Theorem 1 recovers emission grouping, approximate decoding and transitions, and a policy cover. Sample complexity is polynomial for fixed parent width; efficient runtime is conditional on efficient computational oracles. This is substantially stronger than a baseline saying only that factorial HMMs have distributed latent variables.

Audit consequence: unknown coordinates, nonlinear local transition tables, and avoiding exponential joint states do not by themselves distinguish the new target. A contribution must establish something additional, such as lossy history-dependent observation, unsupplied local cardinalities, nonunique realizations, implementable interface discovery, or coherent crossing.

### Discrete latent graph discovery can recover unknown latent counts

Yuqi Gu, *Unfolding Tensors to Identify the Graph in Discrete Latent Bipartite Graphical Models*, arXiv:2501.10897v1. Primary: https://arxiv.org/html/2501.10897v1

Theorem 1 constructively identifies latent count and bipartite loading graph, permitting nonlinear conditional dependence. It assumes two pure observed children per latent and relevant rank/nondegeneracy conditions. The construction examines unfoldings of the population observation tensor; Corollary 1 reduces to marginals of size twice the latent count, not fixed-width marginals independent of that count. The proof uses exponentially large latent-indexed unfoldings. Graph identification does not automatically identify every parameter; Section 4.3 distinguishes these claims.

Audit consequence: a pure-view or multi-view measurement construction must be compared against this result. Discovering the number of latent variables is already an established kind of theorem. Avoiding exponentially large observation tensors, recovering recurrent mechanisms, and deriving operational interfaces would be separate burdens.

### Factored predictive states already trade local scope against prediction quality

Wolfe, James and Singh, *Approximate Predictive State Representations*, AAMAS 2008. Primary: https://www.ifaamas.org/Proceedings/aamas2008/proceedings/pdf/paper/AAMAS08_0647.pdf

Section 4 builds one predictive model per observation dimension, allowing overlapping selected observation scopes. Theorem 5 gives rank monotonicity under enlarging scopes; Theorem 7 gives expected KL improvement from conditioning on more observed history. Exact independent factorization uses an additional conditional-independence assumption. General joint predictions combine local models by a chosen chain-rule order; different orders may give different approximations. Models are learned empirically from a single trajectory, without first learning a whole predictor.

Audit consequence: local predictive summaries, scope selection, and avoiding a global predictor are not new in themselves. The additional issue is whether a chosen collection has one positive recurrent implementation with legal communication and consistent shared randomness, rather than merely useful local predictions.

### Compact distributed automata can be learned from execution queries

Muscholl and Walukiewicz, *Active Learning for Sound Negotiations*, LICS 2022. Primary: https://arxiv.org/html/2110.02783v2

Theorem 7.9 learns sound deterministic negotiations from membership queries on executions and equivalence queries returning counterexample executions. Query complexity is polynomial in negotiation size rather than exponentially larger global configurations. Theorem 6.4 uses stronger local-path queries. The input includes a distributed alphabet specifying the processes participating in each action. Soundness and deterministic negotiation structure are essential. Proposition 4.5 supports canonical minimization via local paths.

Audit consequence: reconstructing local state without global configuration enumeration is established under a strong active-query and supplied-process-domain regime. Passive noisy readouts, unknown action ownership, positive stochastic kernels, and resource-bounded interfaces are not delivered merely by invoking this theorem. Conversely, if a new construction supplies domains and equivalence queries, credit the prior algorithm rather than claim fresh distributed discovery.

### Positive realization has an established cone characterization

Anderson, *Realization problem for hidden Markov models*, Mathematics of Control, Signals, and Systems 12 (1999), 80–120, DOI: https://doi.org/10.1007/PL00009846 . Institutional author record: https://researchportalplus.anu.edu.au/en/publications/realization-problem-for-hidden-markov-models/ . Also Monras and Winter, *Quantum Learning of Classical Stochastic Processes*, TQC 2014, https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TQC.2014.99 .

The classical positive-realization problem starts with output-string probabilities or a linear quasi-realization and asks for a finite stochastic hidden-state implementation. Invariant finitely generated cones are an established characterization. Low linear/predictive rank does not itself supply such a realization. These claims are old baselines, not proposed innovations. The Anderson institutional record was inspected; no theorem numbering from its paywalled full text is asserted here.

Audit consequence: a new theorem cannot consist only of restating cone positivity, adding local factor labels, or showing a rank gap. It must establish how appropriate local cones/factors/interfaces are discovered, when they assemble into one process, and the precise resource and observational equivalences retained.

## Target fidelity gates

The following gates are our proposed audit criteria, not claims extracted from the cited literature.

1. **Unknowns must remain unknown.** List supplied channels, action labels, bounds, observation grammar, sampling facility and quantitative margins separately from inferred local state spaces, channel ownership, wiring, kernel tables, interface signals and memory. A theorem can legitimately restrict the universe; it must not quietly supply a pure measurement for every component or an operation revealing membership and call the core inference solved.

2. **No disguised global enumeration.** Bound every empirical table, history scope, search set, intermediate tensor, oracle and certificate. A fixed local parameter does not make an algorithm polynomial if it calls a whole-state equivalence, filtering, partition-function, or exact optimization oracle of exponential cost.

3. **Predictive state is not automatically local state.** A statistic computed from all past channels may predict a local output but be inaccessible to the component that would own it. Prove its recursive update using only declared inputs and stored state. Include startup and conditioning, not only steady-state update equations.

4. **Stochastic mechanisms need actual joint randomness.** Locally normalized tables do not determine a shared global law unless independence, common-source ownership or explicit coupling is supplied and verified. A correlation variable may not be regenerated independently at each occurrence. Histories sampled in different runs may not be assembled into nonexistent joint observations.

5. **Resource accounting must survive representation changes.** Moving a delay register into its source component, splitting a component, merging adjacent components, sharing a random tape, or moving computation to a sensor can invalidate a claimed lower bound. Report the allowed resource tradeoff, not a preferred syntactic location as physical necessity.

6. **Retain ambiguity at the right level.** Readout-equivalent models need not be related by state permutations. They may have different state cardinalities, ownership, interfaces or temporal correlation. Observational equivalence alone does not identify causal wiring or hardware. Restrict the claim to the specified universe and accessible observations.

7. **Finite tests need a horizon theorem.** A finite list of observed moments or words certifies an entire process only under stated closure/rank/state bounds. Identify what bounds the length of a distinguishing test, and whether that length grows with the joint state count. Empirical agreement is not exact whole-law membership.

8. **Crossing is a separate obligation.** Two local decompositions of compatible observations need not possess a common refinement within the memory/communication budget. Supply actual matching witnesses or an explicit obstruction. Do not define compatibility to mean the desired witness exists and count that as a criterion.

9. **Finite-data robustness needs margins and coverage.** Positivity alone does not prevent observationally near-indistinguishable architectures. Declare conditioning, minimum probabilities, mixing or independent-run access, and quantitative separation. Distinguish exact population discovery from statistical recovery and physical validity.

10. **The promised growing family must carry the difficulty.** A fixed interacting gadget copied independently many times does not demonstrate scalable interacting discovery unless component boundaries are genuinely hidden and interactions between copies contribute to the inference and interfaces. Likewise, recovering a global HMM then renaming its states as tuples does not meet the target.

## Provisional conclusion

A fair candidate contribution is a readout-to-local-realization theorem that derives positive mechanisms and legal finite-memory interfaces under genuinely lossy observations, with explicit ambiguity and constructive joint/crossing witnesses. None of the inspected baseline statements immediately supplies that conjunction. This is a description of the outstanding burden, not a claim that no prior work has it or that the burden has been met.

## Additional partially observed baseline

Katt, Oliehoek and Amato, *Bayesian Reinforcement Learning in Factored POMDPs*, AAMAS 2019. Primary: https://www.ifaamas.org/Proceedings/aamas2019/pdfs/p7.pdf

The model retains a posterior over unknown graph topologies and conditional probability tables under partial observability. Thus structural uncertainty and positive joint models under lossy observations are not unprecedented. The state and observation feature spaces are supplied; the graph and parameters vary. Theorem 1 gives planning-value convergence relative to the Bayesian belief, while Theorem 2 gives asymptotic posterior-sampling consistency for the reinvigoration procedure. These are not finite-sample identification, unknown feature-space discovery, or polynomial runtime guarantees. Correct comparison must credit its ambiguity-aware factored generative modeling while retaining those distinctions.

## 9. Closest comparison to the emerging patch-atlas route

Yao et al., *Multi-View Causal Representation Learning with Partial Observability*, [primary full text](https://arxiv.org/html/2311.04056v2), assume smooth invertible observation maps of overlapping subsets of latent variables and a positive smooth joint latent density. Theorem 3.8 identifies shared content blocks with unknown content sizes (the per-view latent dimensions are supplied). Corollary 3.9 identifies intersections; Corollaries 3.10 and 3.11 identify complements and unions under additional independence conditions. The paper explicitly connects isolating variables to subsequent causal discovery. This is a direct baseline for the overlap/identifiability algebra, not a distant analogy. Its global optimization is not a constructive finite-sample polynomial algorithm; observation maps differ from non-injective noisy finite-alphabet emissions. A new result must distinguish those concrete burdens rather than present overlapping-view discovery as unprecedented.

Huang et al., *Latent Processes Identification From Multi-View Time Series*, [IJCAI 2023 primary paper](https://www.ijcai.org/proceedings/2023/0428.pdf), Theorems 1 and 2 address latent dynamics and alignment of overlapping view-specific sources. The technical development uses full-rank linear VAR dynamics with additive independent noise, differentiable injective observation maps, and population contrastive minimizers. Non-Gaussian/non-isotropic conditions sharpen the residual ambiguity. Shared-source dimensionality is supplied in the merging construction. The results are not finite-sample positive finite-state architecture identification, but they preclude describing multi-view temporal source alignment itself as a new mechanism.

## 10. Patch-atlas-specific fidelity checks (original assessment)

The current candidate has three separately declared promises: measurement patches with three conditionally independent full-rank noisy views; an overlap geometry that isolates latent atoms; and bounded-parent positive Markov dynamics. None individually provides the whole answer, but their combination creates a deliberately favorable identification universe. That is acceptable only if prominently stated and contrasted with the earlier reset model.

1. **Measurement structure is supplied.** The learner does not discover which sensors form independent triples. Prove unknown cardinality/emissions within a bound, but do not claim unrestricted sensor grouping discovery. Explain why patches are not the desired components and why crossing overlap is substantive.
2. **Atoms versus labels.** Finest overlap-information atoms are a canonical observational target. Atoms always co-occurring across all patches cannot be uniquely split by this information; nested incidence permits non-coordinate gauge changes. Do not claim physical component uniqueness or ignore these alternatives.
3. **No hidden exponential atlas.** Derive overlap relations from bounded pair-patch tables, construct closures inside bounded patch state sets, and count all generated equivalence relations. A final test that enumerates all joint patch assignments or all global states defeats the scaling claim.
4. **No secret global decoder.** Learned latent variables are distributions/identifiable labels, not individually known states from noisy readouts. A mathematically valid local mechanism does not automatically supply a real-time state estimator. If interface implementation requires latent state, mark the distinction or provide its filtering realization and cost.
5. **Support reconstruction robustness.** Exact zeros in deconvolved pair-patch distributions establish deterministic overlap; they are not directly observable zeros. Require a positive-mass gap, conditioning bounds and a threshold argument. Full support of the global latent product does not give a useful uniform lower bound unless quantified.
6. **Parent test complexity.** Comparing every candidate S of size d against every extra T of size d uses at most 2d current atoms plus a next atom, but their measurement cover may be larger. Bound the union of selected patches and resulting observation tables explicitly. Full support must include permitted action contexts; observational dependence is not intervention equivalence without a causal sampling assumption.
7. **Minimality is relative.** Controlled lumpability yields a coarsest state quotient respecting chosen responses and allowed incoming signals, not globally minimum distributed memory under arbitrary relocation, randomized interfaces or retiming.
8. **Crossing is a theorem burden.** Grouping identified atoms in two ways is easy; retaining the same coupled execution through both factorizations and interfaces, or diagnosing failure, must be explicit. Independent local marginals do not establish the common coupling.

These checks do not invalidate the candidate. They locate exactly where an end-to-end result could exceed a concatenation of identification, sparse dependency learning and automaton minimization lemmas.

## 11. Temporal product rigidity: an exact classical baseline

Westwick, *Transformations on tensor spaces*, Pacific Journal of Mathematics 23 (1967), 613–620, [primary full paper](https://msp.org/pjm/1967/23-3/pjm-v23-n3-p21-p.pdf), Theorem 3.4 on pages 617–618 characterizes a linear map between different tensor products that sends every nonzero decomposable tensor to a nonzero decomposable tensor. Domain factors are partitioned into groups; each group maps linearly to one target factor, with any unused target factors fixed. Theorem 3.5 specializes to onto self-maps. This is the relevant baseline, not just equal-shaped matrix rank-one preservers. The later *Transformations on tensor spaces II* (1995), [publisher abstract](https://doi.org/10.1080/03081089508818422), broadens the preserver setting; its full text was inaccessible in this audit and is not needed for the application below.

**Application to candidate discovery (our derivation, not a quoted theorem).** A bijection of a finite product alphabet is a permutation matrix on probability vectors. If it takes every strictly positive product distribution into a product distribution under a proposed target Cartesian factorization, the target rank-one minors vanish on an open product-simplex set. Homogeneous polynomial continuation extends this to all product tensors. Invertibility supplies Westwick's nonzero condition. Onto-ness and nontrivial target dimensions exclude unused fixed factors, so target factors are groups of original factors. Basis-permutation structure makes each grouped map a relabeling, up to irrelevant scalar factors in the tensor representation. Hence “universal product preservation implies merging, not mixing” should be explicitly credited as a specialization of a classical preserver theorem.

There are finitely many candidate Cartesian alphabets and labelings for a bounded patch. For every non-coarsening labeling, at least one rank-one minor is a nonzero polynomial in product-law parameters. A generic product law avoids their finite union of zero loci. This gives a route to temporal discrimination of false state coordinates without an exposing sensor cover. It does **not** yet give a numerical margin, data complexity, or show that the actual constrained dynamic parameter family avoids the bad set. If one fixed-context transition row has freely varying positive output distributions independently across atoms, that can supply the noncontainment argument; if parameters are tied across atoms or restricted to uniform output laws, it can fail. The theorem must make this argument in its actual model universe rather than silently replacing the rows by arbitrary independent samples.

## 12. Calibration lemma attribution

Allman, Matias and Rhodes, *Identifiability of parameters in latent structure models with many observed variables* (2009), [author-hosted primary manuscript](https://jarhodesuaf.github.io/papers/Latent.pdf), Corollary 2 gives three-view latent-class identifiability up to label swapping when positive class weights and Kruskal ranks satisfy I1+I2+I3≥2r+2. Three full-column-rank emission matrices meet this for r≥2; r=1 is trivial. This is the direct classical basis for patch calibration. Corollary 2 presumes r; recovering r from a pair-view matrix rank under full-rank emissions and positive weights is an additional elementary argument. Neither result alone is a robust estimation guarantee or evidence that the observed system obeys conditional independence.

Painsky, Rosset and Feder, [*Generalized Independent Component Analysis Over Finite Alphabets*](https://arxiv.org/abs/1508.04934), studies finite-alphabet invertible recoding to reduce dependence without a specified linear mixing model. It provides a useful terminology/computational baseline for the bounded patch factorization search. Only the primary abstract was reviewed in this audit, so no theorem-level subsumption claim is made from it.

## 13. Recursive quotient baseline and non-monotone model scope

Dean and Givan, [*Model Minimization in Markov Decision Processes* (AAAI 1997)](https://cdn.aaai.org/AAAI/1997/AAAI97-017.pdf), Theorem 1 establishes a unique coarsest homogeneous refinement of an initial partition; Theorem 2 justifies separating states with different transition mass into an existing block; Theorem 3 proves the iterative algorithm. This directly covers controlled strong-lumpability refinement when incoming messages are treated as actions and the initial partition records outgoing response. Their factored implementation discussion also warns that aggregate representation/manipulation may be costly. Our boundary result must therefore locate its additional claim in physical locality, coupled realizations, operational wiring or explicitly restricted resource minimality, not partition refinement itself.

**Scope tradeoff flagged by root.** Independent innovations conditioned on the complete previous state permit nonlinear interaction and common lagged-mode parents. They do not permit arbitrary contemporaneously correlated innovations. Adding a same-tick shared source changes the phase order and conditional factorization; it cannot be silently absorbed into a theorem using simultaneous product rows. The preceding source-ambiguity result permitted correlated positive source processes. Accordingly the new theorem can be stronger on unknown states, mechanism discovery and nonlinear dynamics while narrower on innovation correlations. It is not a strict superset without a separate shared-source/within-tick DAG extension. Readout identification also does not give a controller free access to the inferred latent state, and successful local product tests certify the global law only conditional on the declared universe.
