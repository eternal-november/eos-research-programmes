# A connected positive-interface theorem under an explicit experiment regime

2026-10-30. Scoped constructive theorem assembled from classical finite probability, experiment determinacy, concentration, causal compilation, and the checked cylinder-comparison theorem. No novelty, efficiency, unrestricted discovery, or whole-contract completion claim.

## A. Operational doctrine

For each source type a, let Omega_a be a finite product of observable coordinate alphabets. A NEW physical activation draws Z~P_a, conditional on all previous complete physical history, with the same unknown normalized P_a. Coordinates are coexisting effects/reports of that activation, released on a FIXED known schedule independent of their latent values. Random release, absence, censoring, or timeout signals must instead be included as observable source coordinates; they are not silently ignored. Querying a coordinate does not change the remaining latent outcome. A source ID persists across queries; it is never resampled when polled again. Source types may themselves be JOINT blocks containing all correlated elementary mechanisms. Different new blocks are conditionally fresh given their chosen type. Unknown dependence omitted from the block invalidates the doctrine.

For a source a, D_a is a finite downward-closed family of cumulative query sets. A query is allowed only if the previously observed set plus the requested coordinate belongs to D_a, and its release time has arrived. D_a describes the TOTAL transcript obtainable from ONE activation, not the individual sensor calls. Thus successive singleton reads on one activation count as a joint read. Joint physical observability and noninvasiveness are assumptions, not consequences of tags. Mutually exclusive intervention outcomes cannot be placed in Omega_a unless they really coexist.

Production programs are finite causal programs built from these source activations, allowed queries, deterministic gates/copies, clocks and bounded delay registers. They may interleave observations from multiple live blocks and adapt later queries/actions to past public observations. The type and maximum number m_a of activations are declared. Every source-dependent physical hazard, resource outcome and terminal mission test must factor through the covered coordinate trace and the declared deterministic plant semantics. Count the cumulative coordinates used by those physical effects together with controller queries when checking D_a; the controller need not observe the entire semantic trace. A physical coordinate can be included as a covered terminal test without being a public controller observation, but its joint dependence with the public trace must then be included in the required calibration coverage. Equality of public transcripts alone is NOT sufficient for an unobserved collision law. Feedback is operationally guarded by causality/time; arbitrary algebraic fixed-point loops are excluded.

Calibration programs are permitted physical programs in the SAME doctrine. A calibration chooses E in D_a BEFORE activating a new source, using only previous completed calibration records, and actually observes all of Z_E from that activation, with a certified worst-case cost c_{a,E}. It drains pending effects and returns the actual plant to a specified safe boundary condition while consuming time/resources. This need not reset or reveal the hidden mechanism. The returned condition and its uniform safety must be justified physically. The source-law stability from calibration to production is a declared transport premise. It is not identified by matching finite samples.

A finite principal family of production programs, their terminal hazard/mission tests, the physical resource accounting and calibration costs are fixed. Programs can be selected from this family using the observed calibration data. No policy may depend on unobserved source values or on a mathematical choice of a supported world.

## B. Exact experiment adequacy and positive extension

Let observed exact marginals be p_{a,E} for all maximal E in D_a. Define

 C_a={Q in probability simplex(Omega_a): Q_E=p_{a,E} for every such E}.

Require C_a nonempty. This is a finite linear feasibility test and automatically retains all overlap consistency; pairwise separator consistency alone is not substituted for global positive feasibility. Choose any Q_a in C_a.

**Positive realization.** At each activation, sample ONE full latent vector from Q_a and store it. Queries return its existing coordinates when released, and every fanout/delayed physical effect uses the same stored vector. Equivalently Q_a factors into a finite chain of normalized conditional kernels; zero-probability conditioning rows may be completed arbitrarily because unreachable. The representation is positive and normalized, although potentially exponential. No minimality claim is made.

**Contextual adequacy theorem.** For every true P_a in C_a, every admitted production program has exactly the same public transcript law, terminal loss and resource law when implemented with P_a as with Q_a. This remains true under arbitrary finite interleaving/revisiting of live IDs and observable adaptation within the query contract.

Proof at one source: after observing z_S with positive probability, the distribution of an allowed next coordinate i is P_a(z_{S+i})/P_a(z_S), both determined by the shared marginals because S+i in D_a. The corresponding Q conditionals agree. Zero-probability histories are null under both. Induction yields equal next-observation laws for every adaptive source interaction. Globally, source freshness means the posterior of a live block depends only on its own recorded queried coordinates; external scheduling can depend on that record but adds no information about its unqueried coordinates after conditioning on the public history. Induct over the causal execution: activation, query, deterministic gate, clock and drain steps all preserve equality. Alternatively, condition on external independent random seeds and induct over each causal source interaction. The complete public transcript law agrees, not merely a list of independent marginal guarantees.

**Necessity for this interface contract.** If some allowed production query set S is not covered by the linear span of actual allowed calibration transcript kernels, there are two positive source laws producing the same calibration evidence but differing on an allowed production test. For unrestricted Boolean sources with calibration subsets E, uniform plus/minus a parity perturbation on an uncovered S gives an explicit witness. Adaptation on fresh calibration blocks does not distinguish it. If calibration can revisit a source, its COMPLETE reachable query sets, not its primitive calls, must be used in this test.

This necessity is for preserving the stated whole contextual interface. A particular mission can demand less: its loss may lie in the experiment row span even when some other admitted transcript does not. Requiring full contextual adequacy is then a sufficient reusable-interface choice, not a theorem that full identification is necessary for that mission.

## C. Finite evidence, adaptation and costs

Use complete calibration transcripts from sets E chosen BEFORE their fresh activation to estimate all required p_{a,E}. Choosing E after seeing coordinates of the same activation generally selection-biases naive marginal counts and is not allowed by this estimator. For finite alphabets and all possible eligible sample counts, choose union-bound Hoeffding confidence intervals for each cell. Predictable experiment selection does not change the conditional source law. With, for example, per-cell/count error allocations proportional to delta/(number of cells times n^2), the true marginals lie in every interval simultaneously with probability >=1-delta. Optional stopping is covered by this single event.

Let C_{a,t} be the normalized positive source laws satisfying all intervals at time t. Intersect with previous confidence constraints if desired. A true-world coverage event ensures these sets are nonempty. An empty computed set triggers an inconsistency outcome, never vacuous safety. Choose ONE Q_{a,t} in C_{a,t} for an executable positive representative; do not fit incompatible local rows separately.

For a fixed candidate production program pi, compute

 U_t(pi)=sup_{P_a in C_{a,t}} Pr_P[mission failure OR physical violation by the end of all delayed effects].

Use computable outward RATIONAL bounds for numerical confidence endpoints before forming the polytopes. Then this is finite polynomial optimization over compact rational polytopes, hence an exact real-algebraic decision problem; it is not claimed cheap. It verifies a supplied fixed program, rather than solving an arbitrary unknown control game or choosing a hidden-world policy. Equivalent explicit confidence error bounds may replace exact optimization if sound.

Because the confidence event is simultaneous over all P and all times, the data-dependent choice of pi and stopping time is permitted. Only execute if U_t(pi)<=alpha and the ACTUAL remaining physical resource state admits its certified envelope. This alone bounds the event ACCEPTED-AND-FAILED by delta+alpha+rho_cal, where rho_cal bounds acquisition failure. It does NOT bound total mission failure if refusal/abort counts as missed completion. For that stronger claim, add the probability of no certificate, or prove that a usable program is selected on every confidence-good, calibration-successful record. Section G supplies such a finite-sample margin theorem. All production tail effects remain in scope.

Calibration and production cost are not conflated with information refinement. Each calibration step changes the physical state and remaining budget; it is admitted only when its worst-case cost and drain preserve a reserve for some candidate mission. At a fixed boundary state/budget, replacing C by a subset cannot destroy an existing robust certificate. Running an experiment does not satisfy that fixed-boundary hypothesis automatically.

A positive acquisition theorem requires a budget margin: if a finite calibration design has sufficient counts to make some fixed pi satisfy the robust loss threshold, its total costs plus pi's envelope fit the initial budget, and every calibration step is safe/admissible, executing that design yields the certificate with probability >=1-delta. These premises can be checked from the displayed concentration bounds and known cost envelopes. If no such design fits, failure of this construction is not physical impossibility. The experiment-indistinguishability pair above proves only the stronger statement that no strategy in that observation regime can determine the differing contextual quantity.

## D. Independent capability matching

The controller is a finite typed program. Its compilation certificate lists required primitive actions/sensors, maximum live source IDs, memory per ID, clock/delay capacity, and a worst-case action/time/resource envelope over all observation branches. A constrained agent declares executable primitives with their refinement maps and capacities. Matching is primitive inclusion plus componentwise resource bounds and preserved timing order.

Induction on the finite program syntax proves: a matching witness realizes the same causal kernel and respects its resource envelope. This is a simple sufficient compiler/refinement theorem, independent of the robust probability optimization. It is not complete for every agent or an optimal policy synthesis result. Absence of a matching witness does not establish inability of every possible implementation.

The positive Q interface is an executable stochastic model/simulator used by the certificate; the deployed controller still interacts with the real P source. Capability matching does not magically replace the physical plant by Q or grant control of hidden randomness. The SAME program, source interface family and physical envelopes are used in the probability, timing and capability judgments. A different surrogate cannot be substituted for one check without a new comparison/transport proof.

## E. Actual two-sided cylinder bridge

Each Q_a realization is an honest positive finite stochastic component. Finite time-unfolding yields the actual normalized joint preparation/test probabilities from a causal circuit. Deterministic copying copies one realized value, not independent samples. Shared source nodes remain joint nodes.

Use the full small skeleton Mat_{R>=0}: objects are natural-number-sized finite alphabets, arrows are all nonnegative real matrices, and tensor is Kronecker product. Represent stochastic kernels by their column-normalized arrows. This matrix category has fixed tensor-product wire objects and the algebraic duality used by the previous compact-boundary construction. Its cups/caps need not be normalized stochastic operations; they are proof tools, never additional executable interventions. Only the original causal diagrams supply normalized operational arrows.

For a fixed supported family P=(P_a), give each component its full labelled preparation/test factorization, including its ports. Concretely the preparation leg retains the incoming action/context and samples one source state; the test leg applies the allowed causal coordinate readout/deterministic gate, retaining latent state when it will be reused. The usage monitor for cumulative coordinate sets is part of the operational state/type. Preparation/test indices contain ONLY these admitted interventions and readouts: no arbitrary hidden-state tomography, prohibited cumulative query union, or transport-changing intervention is inserted by the matrix embedding. The checked compact-boundary theorem constructs the honest raw network realization and its M-left/E-right comparison to the canonical free-Isbell cylinder middle. The earlier signed-context family theorem gives the coherent comparisons under the declared wiring, gluing, interventions and guarded finite-horizon feedback. This is performed over the discrete supported-P base and the declared preparation/test categories, preserving their variance.

At exact evidence, Section B identifies ONLY the actual admitted EXTERNAL API/mission cylinders for P and Q, hence their canonical CFS middles agree up to the unique leg-preserving comparison appropriate to that SAME external cylinder. Their full latent-Omega source cylinders can differ. No local middle with an exposed full-Omega output is identified across P and Q, and no arbitrary Mat test of a private latent wire is admitted. Network coherence is established separately at each fixed P; P/Q comparison occurs at the common restricted external cylinder. Raw operational carriers can differ. At finite confidence, external cylinders need not agree: retain the family indexed by P and the operational uncertainty bounds. There is no automatic exact Isbell isomorphism or numerical metric on free apices supplied by the concentration theorem. Evidence restriction simply restricts this family.

Thus the connected chain is: permitted charged experiments -> jointly feasible positive source family -> one normalized executable representative plus robust certificate -> independently matched causal implementation -> actual normalized mission cylinder -> existing coherent two-sided comparisons. No leg assumes a positive realization merely from real-linear rank factorization.

## F. What remains hard beyond this theorem

The chain requires known source boundaries, known non-invasive cumulative query regimes, source-law transport, and certified calibration safety/drain. It does not discover those premises from behavior. Nor does it provide compact positive realizations, learn unknown architectures, establish unrestricted stochastic feedback, close crossing/equipment/repair clauses, or prove novelty. Most ingredients are classical and the categorical linkage reuses v2.

The central stronger implication still missing is: from limited safe evidence with uncertain coupling/transport, produce or validate the required operational source/interface boundaries and context-admission laws, with a positive realization, WITHOUT assuming those laws and WITHOUT identifying all hidden mechanism details. Adversarial indistinguishability can make this impossible in some regimes; a useful positive theorem needs explicit experimentally attainable structural conditions weaker than full joint-kernel access.

## G. Fully specified growing shared-warning/delayed-load family

This family proves a connected chain with learning, stochastic realization, capability matching, timing/physical assurance and completion. Its mechanism, gate and probe premises are deliberately explicit.

A real activation produces an immediate warning X in {0,1} and a delayed load bit Y in {0,1} released exactly L>0 ticks later. Sensing and gate-decision latency is a certified g<L; f and b include this latency, so the chosen gate state is established before release. The unknown four-cell law p is arbitrary. Activations are fresh conditional on history. A physical gate multiplies the released load: with the gate disabled, the event is safe; with it enabled, Y=1 is a violation. Gate operation does not change the source law. This is a causal physics premise, not estimated transport. A safe calibration keeps the gate disabled, records the actual X and Y of one activation, waits L and drains it. Its certified cost c_cal>=L includes setup, readout, logging and count updates; L alone is only the physical waiting component. It does not reset or reveal the underlying mechanism. Individual X-only and Y-only calibration are also possible but generally insufficient.

The production program consists of n required jobs. It observes X for each job: X=0 chooses a fast gated branch of duration f; X=1 chooses a gate-disabled bypass of duration b>f. Require f>=L, so each event's delayed physical effect resolves by the end of either branch. Jobs are sequential; source memory is one ID/two bits plus countdown and loop index. At service deadline T the program stops and performs a final certified drain, at most L ticks. Noncompletion by T is failure. Any active physical load before cutoff remains in the safety event. The program never samples a new state when revisiting a source ID.

Write p_xy=P(X=x,Y=y). A safe completed fast job has mass p_00 and duration f. A bypass has mass p_10+p_11 and duration b. Therefore exact probability of safe completion of all n jobs by T is

 s_n(p;T)=sum_{j=0}^k binom(n,j) p_00^(n-j) (p_10+p_11)^j,
 k=min(n, floor((T-n f)/(b-f))),

with s=0 if T<n f. This is the coefficient sum of [p_00 z^f+(p_10+p_11)z^b]^n through degree T. The bounded-stop implementation has exactly this success event; paths not completing by T count as failures, not discarded trials. No optimizer chooses a different action in different hidden worlds.

### Separate capability witness

An agent must provide the warning sensor, delayed-load observation during calibration, gate enable/disable actions, clock resolution for L,f,b,T, one live-source memory slot, two outcome bits and an O(log n) job counter. A typed compiler maps the branch-and-loop program to these primitives. Its induction invariant tracks the one live ID, gate state, pending deadline and remaining jobs. Matching checks these features and capacities; it does not solve a hidden-state planning game. If the physical platform cannot implement the guarded branch or drain, this certificate is unavailable rather than silently assuming the controller exists.

### Finite budget sufficient completion theorem

Choose risk alpha and confidence delta in (0,1), and a strict gap eta>0 with 1-alpha+eta<=1. Perform m safe paired calibrations, costing at most m*c_cal; let phat be the empirical four-cell distribution. Set

 epsilon is any declared rational number >=sqrt(log(8/delta)/(2m)),
 lower=max(0, s_n(phat;T)-2n epsilon).

Accept the production program iff lower>=1-alpha; otherwise safely abort, COUNTING the mission as missed. The positive interface is the empirical four-cell source, sampled once per activation and routed through the actual gate/delay program. A confidence family can be retained alongside it.

If (i) the true p satisfies s_n(p;T)>=1-alpha+eta, (ii) m >= 8 n^2 eta^(-2) log(8/delta), (iii) the platform has the capability witness, and the SAME declared epsilon satisfies 4n epsilon<=eta, and (iv) the overall time budget B is at least m*c_cal+c_check+T+L and the calibration/drain envelopes are admitted, then:

- acquisition is safe and consumes its stated budget;
- with probability >=1-delta, the algorithm ACCEPTS, rather than merely being safe if it accepts;
- including safe abort as missed completion, total probability of mission failure or physical violation is <=delta+alpha;
- every execution respects the hard overall time budget B, including the final delayed-effect drain.

Proof: With probability >=1-delta, all four empirical cells differ from their true values by <=epsilon, by four Hoeffding bounds and union. On this event TV(p,phat)<=2epsilon. Coupling each fresh activation once gives TV(p^n,phat^n)<=2n epsilon. Deterministic causal branch/timing/physical processing cannot increase this, so |s_n(p)-s_n(phat)|<=2n epsilon. The sample bound permits the rational choice epsilon=eta/(4n) when eta is rational; use that choice or any valid smaller declared radius. The required inequality 4n epsilon<=eta then gives lower>=s_n(p)-4n epsilon>=1-alpha and acceptance is guaranteed on the same event. The test also gives true success>=1-alpha on that event. Production activations are fresh after calibration, so conditional production failure is <=alpha for every good calibration record. Bad calibration records, including all false rejection, cost at most delta. The time bound follows from m full calibration costs, a certified checking/compilation reserve c_check, bounded service cutoff, and final drain. Checking is not assumed instantaneous. The guarantee is not claimed when no strict gap or sufficient budget exists.

The crude n^2 sample bound can be improved using direct confidence for the relevant two-dimensional statistics or the exact robust polynomial; no optimality claim is made. The important point is the explicit finite condition ensuring actual useful completion, not just accepted-run safety.

### Shared dependence is mission-relevant

For n=10, choose k=3 (T=10f+3(b-f)). Two positive source laws have identical marginals P(X=1)=P(Y=1)=0.1:

 p^+=(p00,p01,p10,p11)=(0.9,0,0,0.1),
 p^-=(0.8,0.1,0.1,0).

They have different safe timely completion probabilities given by the formula above. Every separate marginal test, even with arbitrarily many fresh samples, is identical between them. The paired experiment distinguishes them using one actual activation, not cloned counterfactual randomness. Timing is nontrivial because more than three bypasses misses the deadline; physical safety is nontrivial because p01 can cause a fast-branch violation. Source response dependence matters to their combined guarantee.

The learned interface is four-state positive, but no hidden physical mechanism or internal parameterization is identified. The family grows in number of jobs and budget/capability demands; it does not manufacture irrelevant hidden coordinates to claim nonidentification. Decomposition here retains the joint warning/load source instead of replacing it by independent sensor and load marginals.

### Contract scope of this connected result

The family meets a concrete evidence-to-positive-interface-to-matched-program-to-safe-timely-completion chain under explicit source/gate/calibration premises. Its causal matrix circuit supplies the Section E two-sided comparison family on the SAME learned/source object. It still does not learn the causal gate law, the calibration/production transport, unknown source grouping, general architecture, or the full retained structural equipment and repair obligations. This is a positive scoped end-to-end theorem, not the final contract or a demonstrated new research theorem.

## H. Strengthening: partial joint identification on the SAME route-selection family

Replace the single load by two simultaneously existing route loads F and S, with early warning W. A physical event creates Z=(W,F,S) before any gate choice. The gate can expose at most one route per event and does not alter either latent load. Actual acquisition hardware can read (W,F) or (W,S) with gates disabled, but cannot read both loads from the same activation; each route is selected before a fresh calibration activation. These are coexisting physical quantities, not hypothetical outputs of mutually exclusive interventions. The limited readout/gate regime is a declared operational constraint, not inferred from data. If in reality choosing a route changes the other response or the source law, this model does not apply.

Production observes W and chooses fast route F when W=0 and slow route S when W=1. The selected route incurs violation iff its delayed load is 1. Latencies and safe calibration/drain premises are as in G. Cumulative relevant coordinate sets are {W,F} and {W,S}; no admitted current mission uses {W,F,S} jointly. The actual joint triple law P is unknown.

### Exact positive extension without learning the triple

Let p_F(w,f) and p_S(w,s) be the two exact observed pair laws. They have the same W-marginal p_W because they arise from the same source law. Conversely ANY two nonnegative normalized pair laws with the same W-marginal have the positive joint extension

 Q(w,f,s)=p_F(w,f)p_S(w,s)/p_W(w) when p_W(w)>0,
 Q(w,f,s)=0 when p_W(w)=0.

This is normalized and has both measured pair marginals. Its conditional-independence form is a REALIZATION CHOICE, not a claim that the physical F and S are conditionally independent. Any other positive joint extension gives the same allowed adaptive route-selection law. The shared W is copied; the load query uses the already chosen source state, not a fresh independent report. If storing Q's full triple is undesirable, sample W, then F and S conditionally and retain them; these kernels are normalized on all reachable rows.

The resulting operational interface and the true source have identical admitted preparation/test cylinders, although their triple laws and behavior in a new both-route context can differ. The exact CFS bridge applies to that identical admitted cylinder with its explicit context restriction. An intervention that activates or observes both routes enlarges the required experiment coverage and needs a new check.

The exact success polynomial is the G formula with

 a=P(W=0,F=0),   bmass=P(W=1,S=0),
 s_n(P;T)=sum_{j=0}^k binom(n,j) a^(n-j) bmass^j.

Neither the unobserved F-S correlation nor the whole triple distribution is required for this actual mission. It is nevertheless relevant to a legitimate enlarged both-route context, so the missing distinction is not meaningless hidden padding.

### Finite evidence, global positivity and actual completion

Take m safe fresh calibrations of each route, for total time at most 2m*c_cal, where c_cal includes waiting, setup, sensing, logging and counter updates. Form all eight pair-cell empirical frequencies. Declare a rational epsilon>=sqrt(log(16/delta)/(2m)). Define C as the simplex of triple laws whose two pair marginals lie within epsilon of the corresponding empirical cells. Use this SAME epsilon in the intervals, certificate and margin bounds; any outward rounding must be charged by increasing epsilon everywhere. On a single event of probability >=1-delta, the true P belongs to C. The separately estimated W marginals need not agree, which is why they are NOT naively glued as exact laws. Solve the ONE joint feasibility problem; if C is empty, abort and count a missed mission.

Choose any Q in C and compile its positive route interface. The candidate completion certificate is

 lower=max(0,s_n(Q;T)-4n epsilon).

For any P',Q in C, their relevant masses a,bmass each differ by at most 2epsilon. The total variation of the collapsed one-job law (safe-fast, safe-slow, failure) is at most |a_P'-a_Q|+|b_P'-b_Q| <=4epsilon. A fresh-source coupling once per event and deterministic timing processing give |s_n(P')-s_n(Q)|<=4n epsilon. Hence lower bounds success simultaneously for every P' in C, despite Q being chosen from the same evidence.

If the true law has s_n(P;T)>=1-alpha+eta and

 m >= 32 n^2 eta^(-2) log(16/delta),
 B >= 2m*c_cal+c_check+T+L,

and the capability/drain/checking premises below hold, choose epsilon<=eta/(8n) while retaining the required concentration lower bound. For rational eta the displayed sample condition permits epsilon=eta/(8n), with a conservatively verified upper bound on the logarithm when computing m. Thus 8n epsilon<=eta. On the confidence-good event C is nonempty and every chosen Q yields lower>=s_n(P)-8n epsilon>=1-alpha. Thus the algorithm necessarily accepts on that event. Including empty-C rejection, other refusal and deadline abort as missed missions, total probability of failure or physical violation is <=delta+alpha. All acquisition, checking and tail costs fit B. Optional early stopping requires the corresponding simultaneous-in-count confidence sequence; the displayed fixed-m theorem needs no optional-stopping premise.

This is a strictly partial joint-identification theorem with a positive reusable source realization, an explicit finite safe acquisition budget, a simple capability witness and the SAME adaptive stochastic/timing/physical mission. The general categorical comparison remains exact per admitted cylinder at exact evidence and family-valued at finite confidence.


### Finite checking and memory are charged

The eight empirical cell counters require O(log m) bits each, in addition to source registers and the production loop counter. Confidence intervals and epsilon are rational. Feasible C has eight unknown cell probabilities, one normalization equality, eight nonnegativity inequalities and sixteen marginal-interval inequalities. A deliberately simple finite exact solver enumerates seven candidate active inequalities among these 24, solves the resulting eight-by-eight rational linear system with normalization, and retains the first feasible solution. Any nonempty bounded polytope has a vertex; a vertex supplies seven independent active inequalities together with normalization, so this algorithm finds a rational Q whenever C is nonempty. Singular candidates are skipped. At most binom(24,7) candidates are tested. This is an explicit finite algorithm, not an assumed cheap optimizer.

Evaluate s_n(Q;T) exactly using rational arithmetic and at most O(n^2) elementary rational operations (or a sharper recurrence). Intermediate bit lengths are bounded from n and the rational input bit lengths using standard determinant/elimination bounds. The capability witness must provide sufficient arithmetic workspace, counter storage and a certified execution-time bound c_check for this finite solver, probability evaluation, certificate check and controller compilation. The hardware clock/time budget uses that certified bound; no universal real-time hardware speed is inferred from finiteness. Source model simulation is not required on the real controller: Q is used for verification, while production acts on the real source.

### Concrete unidentifiable distinction

Let W~Bernoulli(0.1). Independently of W, compare two physical load couplings, both with P(F=1)=P(S=1)=r:

 correlated: P(F,S)=(0,0) with 1-r and (1,1) with r;
 exclusive: P(F,S)=(0,0) with 1-2r, (1,0) with r, (0,1) with r.

For 0<r<=1/2, both are valid, and the two permitted pair experiments have exactly the same laws. Every current route-selection mission has success (1-r)^n times the Binomial(n,0.1) probability of at most k slow branches. A new context activating both routes has probability of at least one load failure r versus 2r. No amount of permitted pair calibration determines that enlarged-context risk. The conditional-independent extension is a third valid operational representative for the CURRENT context class, not a universal physical reconstruction.

This is the first connected family here that does not reconstruct the entire joint source law before composition. Its proof is classical positive marginal gluing plus finite-context probability comparison and the previously established CFS machinery. The acquisition law, coexisting-coordinate premise and gate/transport semantics remain primitive limitations.
