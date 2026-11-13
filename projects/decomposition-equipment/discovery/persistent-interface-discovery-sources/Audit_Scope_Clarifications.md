# Scope audit: four clarifications

28 October 2026. **Mathematical clarification, not a new theorem milestone or physical safety certification.** This note records the pre-revision audit of the originally delivered synopsis against `Coupled_Family.md` (especially A2 and §4) and `Proposal_Validation.md`. The resulting clarifications were subsequently incorporated into scope clarification revision 1. An independent reread of that revision and the appended source notes found no unintended theorem change. Original-report hashes below identify the audited pre-revision evidence, not the revised deliverable.

## 1. Mixing blocks: identifiable finest partition, not arbitrary labels

**Existing coverage.** A2 defines the graph on observed rows whose edges mean that two rows share an innovation column. Strict innovation biases make the displayed characteristic-moment ratio greater than one exactly on such an edge. Connected components separate the actual indecomposable mixing blocks; A2 explicitly says an originally declared block may split further. Invertibility equates each component's number of rows and incident columns. Local log-Walsh inversion then recovers the columns and probabilities up to latent permutation.

**Smallest synopsis clarification.** Replace “reveals the unknown mixing blocks” with “reveals the finest indecomposable mixing partition, not arbitrary preassigned block labels.” The size-at-most-q assumption is a locality bound. For M=I₂, the finest partition consists of two singleton rows/columns; regarding I₂ as one assigned 2-by-2 block supplies no additional identifiable fact. No theorem repair is needed. These sensor-mixing components are also distinct from the lag-support region partitions.

## 2. Polynomial means a structured, quantitatively conditioned subclass

**Existing coverage.** The report's declared-family and finite-confidence sections state binary linear delayed dynamics; bounded local mixing and recurrence widths; fixed action width; independent strictly biased innovations; known calibrated independent sensor noise; quantitative margins; invertible terminal lag; and a uniform stationary initializer for the clean end-to-end theorem. They distinguish burn-in for transition discovery from reconstruction of unknown initial correlations. The report already charges poor conditioning and potentially large search degree. The stronger Fourier argument removes the optional high-noise contraction inequality, not these structural restrictions.

**Smallest synopsis clarification.** Say: “This demonstrates polynomial inference for this structured subclass at fixed widths, delays, calibration/bias bounds and separation margins—not a general escape from hidden-decomposition discovery complexity.” Terminal invertibility and the known stationary law are substantive assumptions, not implementation conveniences. The exponential predictive-state rank remains a valid representation-size separation, not a universal computational lower bound for other structured learners.

## 3. Proposal acceptance is class-relative

**Existing coverage.** The report explicitly denies that acceptance certifies membership of an arbitrary external world in the class. `Proposal_Validation.md` derives its pairwise criterion from invertible linear mixtures of independent strictly biased innovations, not from a general implication of pairwise to joint independence. It also charges validation width and adaptive proposal selection in the confidence event.

**Smallest synopsis clarification.** Add: “Agreement on these bounded-order statistics does not rule out nonlinear dynamics, correlated noise, or other out-of-class behavior.” Such alternatives may evade these tests; acceptance alone supplies no general misspecification or deployment-robustness guarantee. This does not weaken the exact class-relative verifier.

## 4. Finite-horizon risk transfer: event semantics and confidence

**Existing coverage.** The report and §4 bound H-step action/readout transcript total variation on correct structure and parameter accuracy, under the common uniform initializer, uniformly over observation-history policies (including a policy chosen after learning). They explicitly deny uniform infinite-horizon approximation. Exact indefinite interface identities concern presentations of one fitted model, not indefinite statistical fidelity to the world.

**Precise interpretation.** Let G be the simultaneous learning-confidence event, with probability at least 1−δ under the assumed data-generating family. For each learned output D in G, align latent coordinates and suppose max_i |p_i−p̂_i|≤ε. For the same admissible controller π_D and the stipulated common initialization, let P_D and P̂_D be the true-model and fitted-model H-step deployment transcript laws. Set β=min(1,nHε). For every measurable transcript event A_D,

    |P_D(A_D) − P̂_D(A_D)| ≤ β.

Thus a represented failure event with fitted probability at most r_D has true-model probability at most min(1,r_D+β), **on G**. This is a high-confidence statement about deployment laws; conditioning the training outcome on G must not be confused with conditioning the deployment transcript itself on G. A fresh deployment whose common uniform initial law is independent of training is a clean mathematical instance, not a claim that a physical system can be reset this way. In particular, a continuation after the training trajectory generally has a history-conditioned hidden-state law, not the unconditional uniform law. If an appropriate true/fitted initial-law TV discrepancy ε₀ is separately certified (for example for posterior initialization), the same coupling instead gives β=min(1,ε₀+nHε). No such posterior-initialization certificate is supplied here.

A physical hazard F needs an additional sound relation to a represented event. If separately justified physics/measurement semantics give, for each relevant D,

    P_physical,D(F) ≤ P_D(A_D) + η,

then on G the corresponding bound is min(1,r_D+β+η). Here η is an independently justified hazard-transfer/model-discrepancy allowance; the discovery/checker theorem does not estimate or certify it. An inclusion of F in the represented event under an appropriate sound coupling would give η=0. Without such a relation there is no physical-hazard conclusion. Observability is sufficient for the stated transcript-TV corollary, but not logically necessary for every extension: the proof’s shared-initial-state/innovation coupling also controls represented latent trajectories. Consequently a modeled latent-state hazard can be transferred under a common state/event interpretation and the same initialization conditions. What is missing for an unknown physical hazard is a sound semantic correspondence, not merely an observable alarm.

Optionally, for a joint training-and-deployment experiment with these deployment laws, a uniform fitted-risk bound r_D≤r on G yields an unconditional bound min(1,r+β+η+δ) by charging worst-case loss on G's complement. A slightly sharper version is c+(1−c)δ, with c=min(1,r+β+η). The δ term is a learning-failure budget, not an extra per-deployment error on G. Neither formula is robot safety certification or an infinite-horizon guarantee.

## Disposition

The user's characterization—more substantive but still algebraically engineered—is consistent with the declared theorem family. The proof already resolves the block-identifiability point; the synopsis should name it. Remaining changes are scope wording, especially the distinction between observable event transfer and independently justified physical hazard semantics. No new research claim is required.

Audited report SHA-256: `f867a2df378d6288ef33e3b7ed305ef8898c55223cd528b36f086c6916c5a215`.
