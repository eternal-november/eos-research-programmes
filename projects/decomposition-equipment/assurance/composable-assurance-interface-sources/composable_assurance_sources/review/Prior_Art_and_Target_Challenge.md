# Independent prior-art and target challenge

29 October 2026. Status: prospective review, not an experimental result. Primary sources inspected through search/open; no claim of exhaustive novelty search. No experiment run. Reviewer: challenge_heterogeneous_assurance_target.

## Bottom line

The basic ingredients are established more directly than a generic contracts bibliography suggests. There is already a framework combining tests, formal proofs, imported assumptions, probabilistic contract composition and evidence provenance for learning-enabled systems, demonstrated on sensor-fusion braking. There is already a generic incremental engine selecting local revalidation steps, and there are learned probabilistic assumptions and verified observation-to-assumption monitors. None of those ingredients alone is a credible new target.

A worthwhile scoped target remains: **discover a sound, useful boundary and recursive memory from permitted evidence about an initially unfamiliar subsystem, while retaining unresolved shared dependencies; then make that discovered boundary support different proof methods and non-monotone online maintenance/replacement.** This is a proposed residue, not a literature-wide novelty conclusion. It needs a constructive restricted class and an interacting benefit witness before experiments.

## Closest primary sources and their pressure on the target

1. **ScenicProver**, Vin, Miller, Incer, Seshia and Fremont, 2025 preprint. https://arxiv.org/abs/2511.02164 ; full text https://arxiv.org/html/2511.02164v1 . Supports interpretable and black-box components, temporal assume-guarantee contracts, testing, user-supplied proofs (Lean integration), external assumptions, contract-evidence operators and assurance-case provenance. Its case study is emergency braking with sensor fusion, with stronger probabilistic guarantees than monolithic testing at matched testing budget. The introduction explicitly discusses change-local component re-verification and notes that component specifications still need manual creation or automatic synthesis. Consequently, combining heterogeneous evidence or proving its compositional arithmetic is not enough. Our defensible difference would require discovering interfaces/dependencies from readouts, not merely instantiating their supplied component interfaces.

2. **An Incremental Verification Framework for Component-Based Software Systems**, Johnson, Calinescu and Kikuchi, CBSE 2013. https://eprints.whiterose.ac.uk/id/eprint/75438/1/cbse21_inc.pdf . INVEST uses algebraic system/verification descriptions to select minimal component-wise re-verification after component additions, removals and changes. It integrates probabilistic assume-guarantee verification and reports cost improvements. Its setup supplies the component structure and property map. Thus a provenance graph and selective descendant rechecking are not a sufficient result; a discovered semantic support with justified scope changes would be a meaningful extra obligation.

3. **Automated Learning of Probabilistic Assumptions for Compositional Reasoning**, Feng, Kwiatkowska and Parker, 2011. https://prismmodelchecker.org/papers/fase11.pdf . Algorithmic learning of probabilistic assumptions for compositional model checking is established. The paper builds on earlier learned nonprobabilistic assumptions. Related primary implementation paper: https://www.prismmodelchecker.org/papers/atva11.pdf . Merely learning a finite-state contract then composing it is not a sufficient distinction. Distinguish supplied component models/verification teachers from safe partial-readout identification, and state the actual cost of the latter.

4. **Abstraction and Learning for Infinite-State Compositional Verification**, Giannakopoulou and Pasareanu, 2013. https://arxiv.org/abs/1309.5140 . Interleaves learning and abstraction for compositional verification of infinite-state systems, including interface generation. Therefore adding abstraction refinement to contract learning does not by itself establish the target's distinctiveness.

5. **Monitoring Assumptions in Assume-Guarantee Contracts**, Sokolsky, Zhang, Lee and McDougall, 2016. https://arxiv.org/abs/1606.00505 ; primary institutional full text https://repository.upenn.edu/server/api/core/bitstreams/ae7880bb-dd19-40c4-b97c-079874df3a68/content . Connects pre-deployment guarantee verification with runtime environment-assumption monitoring, including a verification step for the gap introduced by I/O-library transformations. Observation adapters and verified monitors are already substantive prior art, not just implementation plumbing that has gone unaddressed.

6. **Symbolic Runtime Verification for Monitoring under Uncertainties and Assumptions**, Kallwies, Leucker and Sanchez, 2022. https://arxiv.org/abs/2207.05678 . Deals with incomplete/imprecise inputs and execution assumptions; symbolic stream monitoring in richer theories; pruning in Boolean/linear domains preserves full-history inference power with constant memory. A recursive sufficient monitor state or forgetting old records is not enough alone. We must discover what has to be remembered for the heterogeneous obligations, with a clear model-class restriction and cost accounting.

7. **Proof Repositories for Compositional Verification of Evolving Software Systems**, Bubel et al., 2016. https://ebjohnsen.org/publication/16-fomac/ . Incremental proof repositories cache partial proofs for adaptation to implementations and evolving contracts. Reusable proof fragments are another strong baseline rather than a standalone contribution.

8. **Incremental Contract-based Verification of Software Updates for Safety-Critical Cyber-Physical Systems**, Bebawy et al., CSCI 2020. https://www.offis.de/en/offis/publication/incremental-contract-based-verification-of-software-updates-for-safety-critical-cyber-physical-systems.html . Uses contract compliance to focus update verification on changed modules and environment impacts, with adaptive-cruise-control examples. Component replacement through contract compliance is established; discovery and valid online boundary maintenance need to carry the new work.

These are mostly different settings, not a proof that someone already solved the proposed combined problem. Conversely, absence of the complete combination from this short pass is not evidence of novelty.

## Prospective gate: what must be shown before running an experiment

### A. Do not supply the answer as the model universe

Permissible supplied premises: physical meaning and units of signals; trusted timestamp semantics/calibration; an expressible bounded-memory/coupling class; known initial safe region; noise/source-law premises. Unknowns should include actual dependency scopes, relevant history, parameter relations and reusable interface. Supplying a family indexed by the exact desired decomposition or a mission-specific checker disguised as a type fails this gate.

A finite set of observations cannot in general certify that an unexcited dependency is absent. Sound discovery must either (i) retain its possibility, (ii) use a separation/coverage/excitation premise and show how it is met safely, or (iii) rely on a trusted structural witness. The certificate should say which. Merely detecting correlations cannot license noninterference, and absence of detected correlation is even weaker.

### B. Define the actual heterogeneous semantics

Each claim must have a common causal execution interpretation but need not share one solver. A sensing certificate may quantify over a population/source law; a timing monitor over traces; a dynamics witness over all disturbance trajectories. The composition must preserve these quantifiers. Training confidence is not runtime failure probability; a confidence interval is not a deterministic envelope. Shared calibration, common clocks, common power and data-dependent selection must remain shared objects in the semantics.

### C. Require two distinct update laws

*Refinement:* for fixed readout/clock meanings, retained-evidence set reduction K' subset K preserves universally valid old certificates; stronger interfaces may admit additional controllers. Strictness needs a preconstructed controller/mission witness, not merely a finer representation.

*Retraction/replacement:* expiry, source shift or subsystem replacement can enlarge/change K. Old validity is not monotone. Reuse requires a proof that each retained certificate's complete semantic support is unchanged or still entailed. Dependency-graph reachability is only the implementation after completeness of the discovered support is established. A new controller must also preserve statistical coverage premises; physical I/O compatibility alone does not do this.

### D. Prevent optimistic replacement composition

A replacement matching marginal output distributions or each local trace projection can still change joint failures, shared-parameter relations, clock epochs, hidden resource loading or observation-policy dependence. State a relational contextual refinement criterion for the discovered interface. A locally conforming replacement that violates a shared assumption must be rejected or trigger a clearly identified larger recheck. A positive example should include one accepted and one deceptively similar rejected replacement.

### E. Construct a meaningful interaction and prospective benefit

A promising family is a multi-device mission with a shared communication/power or calibration mechanism: actions change both sensing coverage and latency; outstanding commands have epoch/acknowledgement state; delayed dynamics impose terminal reserves. Several safe completion modes should exist and scheduling should depend on learned distinctions. The point is not a handwired sensor-delay-stop inequality, but an initially unknown shared dependency whose discovery changes which compositional proof and controller replacement are valid.

Before outcomes, exhibit (1) two evidence-compatible worlds that agree on a deliberately too-small interface but differ on a relevant composition judgement, (2) an obtainable refinement that resolves the judgement or supports a cheaper reusable check, and (3) the same mission/controller information rights in the baselines. This need not be a large simulation; it does have to rule out the earlier mission-design failure.

### F. Cost must survive serious baselines

Compare against coherent full-model caching and an ordinary supplied-interface incremental proof-dependency checker, not just full reverification from scratch. Count acquisition, interface search, witness construction/checking, representation memory, online invalidation and replacement checks. A semantic reduction without cheaper construction/query cost may still be a useful theorem but must not be called a computational advantage. A discovered local checker that internally calls a full verifier does not pass.

## Current verdict

The authorized target is worth pursuing but **not yet passed**: no concrete constructive class, discovery procedure, interacting strictness/cost witness, or verified update law has been supplied to this reviewer. The correct next milestone is a checked target specification and a meaningful family, not another success-count experiment. No access/authorization blocker was encountered in this review. Literature breadth remains limited; all novelty wording should remain scoped.
