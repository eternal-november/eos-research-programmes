# Safe finite acquisition and mission certificates with unknown linear noise coupling

2026-10-30. A scoped constructive integration theorem, using classical finite-field support learning, linear experiment determinacy, finite policy checking, and the previously checked cylinder comparison construction. No novelty or whole-contract completion claim. Source grouping and filter coefficients are unknown; finite-memory linearity, fresh fair innovations, noninvasive observation and physical isolation remain explicit primitives.

## 1. Physical class and genuinely fresh blocks

Work over F2. There are d observed ports. The autonomous source has an unknown finite number r of innovation coordinates and unknown coefficient matrices A_0,...,A_D in F2^(d x r):

    X(t) = sum_{ell=0}^D A_ell Z(t-ell).

The supplied D is an upper bound, not the actual lag pattern. Every Z(t) is uniform on F2^r and independent across t. Unknown source membership, overlapping XOR incidence and exact lag coefficients are included. Neither the number nor identity of physical innovation sources must be recovered.

After an initial wait of D ticks, define an H-tick observable block at start s by Y_s=(X(s),...,X(s+H-1)) in F2^N, N=dH. It is a known-length linear image of the fresh innovations with indices s-D,...,s+H-1. Consequently its law is uniform on an UNKNOWN linear subspace S <= F2^N. This follows because every fiber of a linear map onto its image has the same cardinality. Unknown r causes no problem: the observable support dimension is at most N.

Starts separated by at least H+D have disjoint innovation-index sets. Thus these blocks are independent and identically distributed even though port values within each block can share arbitrary allowed filter innovations. The initial D wait is charged unless a stationary infinite prehistory is explicitly part of the model. Waiting advances the ordinary physical dynamics; it does not reset, clone or reveal hidden source state.

Safe acquisition uses a certified isolation gate which prevents the source block from causing physical mission hazards while a permitted linear observation A_e Y_s is recorded. A_e is a known physical measurement map, not an assumed counterfactual observation. A complete readout can require a whole sequence of port/time samples; all such samples, release times, readout limits and stored bits belong to this ONE probe. The probe type e is selected before its fresh block begins. The finite design may use fixed start times; any adaptive choice uses only completed earlier-block records and public clock/resource state. Unrecorded source observations in a gap cannot be used to select a favorable upcoming block. No policy may silently acquire a larger cumulative projection by revisiting a block than its hardware/experiment contract permits.

A cost envelope c_e includes at least the complete fresh-start spacing, sensing, storage, finite-field elimination updates and any physical draining beyond stochastic memory D. Each probe reserves its full H+D interval before any next activation, INCLUDING the final calibration-to-first-service transition; a checking pause may contribute to this interval, but is not silently assumed long enough. Service envelopes enforce the same fresh-start condition. Gate noninterference means observation/isolation does not alter A_ell or Z. This and time invariance imply the calibration-to-production block law; they are structural premises, not conclusions of finite samples. Physical draining and stochastic forgetting are different obligations.

## 2. Learn projected support and build a positive interface

Let e=1,...,K be the finite declared safe probe types, with A_e:F2^N->F2^(k_e). For each e collect m_e independent fresh projected blocks. Let Shat_e be their linear span. True S_e=A_e S is uniform and has rank at most k_e. A proper sampled span has a nonzero annihilating functional on S_e. Each specified nonzero functional is zero on all m_e samples with probability 2^(-m_e). A union bound gives

    Pr[Shat_e != S_e] <= (2^(dim S_e)-1) 2^(-m_e)
                          < 2^(k_e-m_e).

For example m_e >= k_e + ceil(log2(K/delta)) makes all projected spans correct with probability at least 1-delta. For K=0 or zero-dimensional probes, handle the vacuous cases separately; the displayed design assumes K>=1 and 0<delta<1. Uniformity supplies the anti-concentration: without it, an unseen support direction can have arbitrarily small mass.

Construct

    Vhat = intersection_e A_e^(-1)(Shat_e).

Check A_e Vhat=Shat_e for every e. If this fails, report inconsistency and refuse; refusal counts as missed completion. The check is essential for noisy/incomplete sampled spans; mere nonemptiness is uninformative because every linear subspace contains zero. On the simultaneous-correct event, true S is contained in

    V = intersection_e A_e^(-1)(S_e),

so A_e V contains A_e S=S_e and the defining constraint gives the reverse inclusion. Every projection check therefore passes.

A basis B of Vhat gives the positive normalized block interface

    U uniform on F2^(dim Vhat),   Yhat=B U.

It samples one latent block, retains it throughout delayed uses, and returns the prescribed linear readouts. This is a realization of all learned projected laws, not a claim to have discovered the actual source basis, number of innovations or filter. A basis change gives the same uniform block law. In particular V may strictly contain S: missing global relations remain genuinely unidentified.

## 3. Derive exact adequacy for a new linear mission interface

This section is an exact statement over the relaxed compatible block class

    C = {T <= V: A_e T=S_e for every e}.

It includes the actual filter block S. It may also contain block laws not realizable by the particular stationary Toeplitz filter subclass. Soundness for the filter follows by inclusion. Necessity or sharpness for the physical subclass must NOT be inferred unless the adverse witnesses belong to that subclass.

For a proposed mission map Q:F2^N->F2^q, let R_Q be the row space of Q restricted to V, and R_e the row space of A_e restricted to V. Then

    Q T = Q V for every T in C
    iff every nonzero chi in R_Q belongs to at least one R_e.       (U)

The right side is UNION of individual row spaces, not their linear span. It is a finite algebraic test. A spanning-union shortcut would wrongly infer every joint law from individual coordinates.

Proof of sufficiency: if QT is proper in QV, a nonzero linear functional on QV vanishes on QT. Its pullback chi is nonzero in R_Q and vanishes on T. If chi belongs to R_e, then chi=lambda A_e on V. Surjectivity A_e T=A_e V forces lambda A_e to be nonzero on some member of T, contradiction.

Proof of necessity: take nonzero chi in R_Q outside every R_e, and Hchi=ker(chi|V). If A_e Hchi were proper in A_e V, some nonzero linear functional lambda on A_e V would vanish on A_e Hchi. Its pullback would have kernel containing the hyperplane Hchi and hence equal chi (over F2; a nonzero scalar multiple over a general field). This would put chi in R_e. Therefore Hchi belongs to C, while QHchi is proper in QV. Uniform laws on Hchi and V have the same complete probe laws but different Q laws.

Thus partial safe evidence can derive a new context guarantee, rather than assuming it. This is finite linear experiment determinacy; it is not claimed new. It preserves the entire Q-output law. A particular mission loss can require less; failure of (U) is not automatically mission incompatibility.

For adaptive observation-based programs, applying (U) to the cumulative linear query map on every reachable branch is a sufficient way to preserve its complete transcript law. It may be stronger than required for a value-guarded policy. The same sampled block must persist across the branch. Complete branch queries, hidden physical tests and timing/censoring observations must be represented; checking individual calls separately is invalid.

A useful mission-relative conservative law also follows: for a FIXED simultaneous linear load test W whose failure is W Y !=0,

    worst_{T in C} Pr_T[W Y !=0]
      = 1 - 2^(-rank(W|V)).

Indeed uniform T gives failure 1-2^(-rank(W|T)), rank is monotone under T<=V, and V itself belongs to C. This is sharp in the relaxed block class. It is a sound bound, not necessarily attained, in the stationary filter subclass. It is not extended to arbitrary adaptive tests by assertion.

## 4. Same-interface mission and separate capability matching

A growing mission has n jobs. Job j has a finite known menu of physical routes r. A route is selected BEFORE its fresh source block. It specifies:

- a permitted linear mission readout Q_jr and a known bad set B_jr in its finite output alphabet;
- a certified worst-case execution/drain duration tau_jr and resource envelope;
- the sensor, gate, finite-field arithmetic, memory and timing primitives required by that route.

Its actual physical violation or missed useful work must be exactly the declared bad event, or soundly bounded by it through a separately proved physical witness. Public-readout equality alone does not establish hidden physical safety. The source is autonomous and gates do not change its noise law. Each new job starts only after the H+D freshness separation and required physical draining, already charged in tau_jr. Different jobs may reuse the SAME learned source interface but not the SAME physical innovation block.

For each route, check (U) using the learned Vhat and actual probe maps. For a covered route compute exactly

    beta_jr = |B_jr intersect Q_jr Vhat| / |Q_jr Vhat|.

Its finite linear image can be enumerated or represented symbolically; no efficient-computation claim is needed. A fixed route sequence has success at least product_j(1-beta_jr), exactly so when the bad-event definition is exact, because its actual blocks are fresh. Its deterministic time/resource envelopes are summed. A data-selected sequence is permitted: on the single simultaneous support-correct event, EVERY covered route law is correct, so there is no post-selection gap.

Capability matching checks each selected route's primitive availability and numerical capacity bounds. It is independent of statistical model selection. The finite schedule check selects among covered matched route sequences satisfying the deadline and required product success. Enumeration is allowed and its worst-case running time must be charged; this is a known finite route-checking problem, not a renamed solution of an arbitrary partially observed control game.

A simpler exact specialization uses only routes whose Q-image avoids B, hence beta=0. Select the shortest matched covered safe route per job. If one exists for every job and the total duration fits, this simple rule is complete for that declared serial menu. No policy depends on the hidden true subspace or physical innovation index.

## 5. End-to-end sufficient completion theorem

Fix a support-learning design as in Section 2, a finite route menu, a failure allowance alpha and the physical envelopes. Let c_check bound projected-support checks, construction of Vhat, union-coverage tests, route-risk computation, schedule selection and compilation on the matched hardware. This bound includes finite field/rational arithmetic workspace and stored sample-basis/counter costs. No computation is instantaneous merely because the algorithm is finite.

Suppose the exact V formed from the TRUE probe supports has at least one covered, capability-matched route sequence whose success is at least 1-alpha and whose service envelope fits deadline T. This is a completeness condition for the proposed experiment language and route menu, not an assumption that a particular unknown mechanism has been identified. The coverage and sequence tests are explicit finite algorithms; no useful certificate is inserted as an oracle.

If the initial hard budget satisfies

    B >= D + sum_e m_e c_e + c_check + T,

with any further final physical tail included in T or explicitly added, the algorithm safely gathers its samples, performs all charged checks, and executes a qualifying sequence when found. On the simultaneous projected-support-correct event it necessarily accepts. All other outcomes, including inconsistency and refusal, are counted as missed missions. Therefore

    Pr[missed completion or physical violation] <= delta + alpha,

provided the acquisition isolation/drain envelope has zero hazard. A justified nonzero acquisition/physical-premise allowance must be added separately. The true source coefficients are fixed across acquisition and production; the probability is over its genuine innovations and any public algorithm coins.

The theorem learns the projected behavioral consequences of stochastic coupling and delayed source incidence sufficiently for specified mission maps; it does not identify coefficient incidence itself. It does not identify the full filter, prove arbitrary boundary transport, or promise a certificate if no covered route schedule fits the experiment budget. At a FIXED physical boundary and budget, stronger evidence can shrink compatible mechanism families without invalidating an existing uniform guarantee. Running an experiment changes elapsed time, pending state and remaining budget; it is not that pure refinement.

## 6. A growing learned-relation chain, not a direct mission probe

This concrete positive family exercises contextual composition. The algorithm is NOT given the following chain equations as facts. It samples local projected supports, derives their annihilating relations, and accepts only after checking the relations and their composite implication.

A block contains early bits r0,z1,...,zn, intermediate registers r1,...,rn at specified capture slots, and delayed physical load d at slot L. Safe probes measure the actual cumulative triple (r_(i-1),z_i,r_i) for i=1,...,n, and the terminal pair (rn,d), on separate fresh blocks. Intermediate registers may arrive later than the z_i they concern; the probe stores the earlier bits until all three captured values exist. These are factual measurements of one block, not cloned counterfactuals.

The successful instances are those whose learned projected supports imply

    r_i = r_(i-1) + z_i   for every i,
    d = rn.

They need not imply independence or reveal the joint law of all early bits. Kernel computations on the empirical spans derive the displayed local relations. On the full-span event these are true support facts. Their sum gives the GLOBAL residual

    e = d + r0 + sum_i z_i = 0

on V, although no calibration directly observes this entire global residual or its full joint input table. The physical mission computes p=r0+sum_i z_i early and uses a known XOR interlock which fails exactly when p+d=1. Hardware must capture the early inputs and complete the n-XOR computation before the delayed load arrives; its known sensing/compute latency, gate delay and tail are charged. The interlock law is a physical primitive. The autonomous delayed port may emit at every tick: the known gate isolates ALL unselected slots and enables only the selected-slot pulse/capture. Its setup, clock precision and shutoff margins are included in the service envelope. Thus the stated physical hazard is p+d_L at the selected slot, not an unguarded hazard over the intervening output stream. The source relation making that interlock safe is learned.

For the visible mission interface Q=(p,d), the learned equality makes its two rows equal on V. Their common nonzero row, when nonzero, belongs to the row space of the measured terminal pair (rn,d). Hence the dual-union criterion is verified: all supported subspaces have the SAME Q-image and Q-law. In every case the residual p+d is zero, proving safety. If p is identically zero, the row-space condition is vacuous and the conclusion still holds.

The certificate is relative to the fixed parity computation and downstream tests of (p,d). It does not assert equality of the entire transcript of all individually read early bits: those can still reveal unresolved dependence. A controller that branches on extra early-bit details requires its own larger cumulative-query adequacy check. Nor does the construction forbid a richer global probe if the real platform permits one; it demonstrates that this local design suffices without buying or collecting that full joint table.

A positive matched implementation needs early-input capture/storage, n XOR gates or an equivalent finite accumulator, a clock, the interlock, and the certified delay margin. With k_e<=3 and K=n+1 probes, m=3+ceil(log2((n+1)/delta)) samples per probe is a simple uniform sufficient acquisition design. All local elimination, implication checking and compilation costs are finite and charged. If the initial budget includes D+(n+1)m*c_probe+c_chain_check+c_service, the full-span event guarantees acceptance and useful safe completion. With deterministic calibration/isolation physics, total failure is at most delta. There is no conditioned-on-acceptance loophole.

### Learn a useful delay instead of supplying its exact value

The productive load slot need not be known. Retain the local triple probes and add endpoint probes (rn,d_ell) for each candidate release slot ell in {1,...,D}, all within a complete safe H>=D+1 window. Here d_ell is the actual delayed-port value captured at that slot; it is not a hypothetical response. Each probe type is chosen before its block. The algorithm derives which endpoint pair supports imply d_ell=rn, then chooses a slot whose measured equality, controller-computation latency, gate timing and service deadline all pass. It does not assume which lag works.

Now K=n+D and m=3+ceil(log2((n+D)/delta)) samples per type is a simple sufficient design. Charge D+(n+D)m*c_probe plus checking, actual chosen-slot service and all drain costs. If the true filter has at least one matching slot long enough to compute and gate the prediction but short enough for the deadline, the full-span event finds it and guarantees acceptance. This is an explicit checkable delay-discovery condition. No such slot means this method does not certify the mission; it does not prove all controllers incapable.

A stationary positive family has all intermediate r_i available at the early slot and d(t)=R(t-L0)+sum_i Z_i(t-L0) for UNKNOWN L0 in {1,...,D}. Its endpoint at L0 is diagonal, while nonmatching endpoint pairs are full whenever their innovation times differ. Thus the successful lag is recovered from actual finite evidence. Both the independent-z and z1=z2 filters below remain indistinguishable on the chosen local relation/endpoint evidence, so learning the useful lag does not force full source recovery.

### Physical realization with unknown source grouping and delays

These are genuine members of the finite-memory class. Choose fresh fair innovations R(t),Z1(t),...,Zn(t). Let r0(t)=R(t), z_i(t)=Z_i(t), and define the intermediate output port

    r_i(t)=R(t-tau_i)+sum_(j<=i) Z_j(t-tau_i),

while the delayed-load port is

    d(t)=R(t-L)+sum_(j<=n) Z_j(t-L).

In a block beginning at s, capture r0,z_i at s, r_i at s+tau_i, and d at s+L. Choose 0<=tau_i<=L<=D and H>=L+1. The coefficient matrices and actual delays are unknown to the learner; the model class only supplies D and the probe/capture schedule. A different actual filter can fail the learned local relations, in which case this certificate is not issued. Source grouping is therefore not inserted as known wiring.

For n>=2 there are distinct physical filters indistinguishable by this selected local design: one uses independent Z_i; another uses z1=z2 from one shared innovation, with all remaining Z_i independent and R independent of them. Every local triple has exactly the same two-dimensional chain-relation support in both filters, because the independent R masks each pair (r_(i-1),z_i); the terminal pair has the same one-dimensional equality support. Yet their full early-input laws differ. Both therefore produce the same learned mission interface and zero residual without full coupling identification. The missing dependence is not an irrelevant added coordinate: a different mission reading z1+z2 distinguishes the filters.

The local measurements were sufficient for this composed mission because their experimentally recovered equations imply its global relation. This is linear-code/circuit reasoning, not an asserted new general causal-discovery theorem.

## 7. A physically realizable coupling obstruction

Take H=1,D=0,d=4. Allowed calibration observes at most TWO coordinates from each naturally fresh block; arbitrary adaptive choices within that cumulative limit and arbitrarily many independent blocks are allowed. Define

    S0 = ker(x1+x2+x3),
    S1 = ker(x1+x2+x4).

Both are images of memoryless linear maps from three independent fair bits, so both are actual members of the source class. Every two-coordinate projection is full F2^2, hence every admitted adaptive calibration transcript has the SAME law in the two worlds.

The one-job mission has two routes. Route0 fails when x1+x2+x3=1; route1 fails when x1+x2+x4=1. A route is chosen before its source activation. Route0 has failure0 under S0 and1/2 under S1; route1 has failure1/2 under S0 and0 under S1. Assume both route durations/resources fit, and that these are the permitted useful mission implementations. Abort is missed completion with failure1.

Any calibration-based policy chooses route0 with the same probability p in both worlds because the entire calibration transcript law agrees. Without abort its world risks are (1-p)/2 and p/2, so worst risk is at least1/4. Adding abort cannot improve the bound: replace an abort with a fair route choice, whose risk is at most1/2 in each world and1/4 in this pair. Fair route choice achieves1/4 in both worlds. Thus no amount of the permitted pair calibration certifies or achieves smaller uniform missed/unsafe risk, although an informed controller has zero risk in either world.

This is an observation-regime obstruction within the physical class, not solver failure. It does not prohibit a new jointly admissible three-coordinate probe. If such probes exist but each costs c and at most m fit, the two-world subclass yields the familiar testing lower bound: a probe of either route parity has likelihood overlap1/2, so terminal classification error is at least2^(-(m+1)) on average over the two worlds; wrong route costs failure1/2, giving worst risk at least2^(-(m+2)). A fair initial route, repeated testing until parity1 appears, then switching, attains that bound within THIS two-world subclass. It is a classical adaptive hypothesis-testing calculation, not a general tight bound for every unknown filter.

## 8. Relation to actual cylinder comparisons

For each physically supported filter, or each relaxed block support when explicitly using the relaxation, the positive interface realizes the actual admitted finite preparation/test cylinder. Uniform sampling from a basis is positive and normalized before any categorical completion is invoked. Keep shared block state throughout all its delayed uses.

Here is the actual typing for one covered mission map Q. Work in the small finite nonnegative-matrix category, whose compact tensor-product structure supplies the ambient dual wires but not extra physical operations. For any T in C, let the finite raw carrier X_T be the SET T. Its preparation p_T:1->X_T is the uniform probability column. Tests are the rows

    m_y^T(x)=1[Qx=y],       y in O=QV.

Criterion (U) makes Q:T->O surjective. The deterministic stochastic matrix q_T:X_T->O therefore satisfies

    q_T p_T = p_O,         m_y^T = m_y^O q_T,

where p_O is uniform on O and m_y^O is its coordinate-indicator test. Both the true raw realization T=S and the maximal positive representative T=V thus factor the SAME labelled preparation/test cylinder through the positive observable realization O. Uniform pushforward is proved by equal linear-fiber cardinalities; it is not assumed. There need not be a leg-preserving map between the two raw carriers themselves.

The predecessor compact-boundary/CFS theorem now supplies an actual comparison span

    X_T <-M U_T ->E R,

and similarly O<-M U_O->E R, to the common canonical middle R of that cylinder. The realization morphism q_T induces the predecessor's SOURCE-CHANGING double cell between these spans. It is not assumed to be E, M, invertible or to have a physically admissible section.

For a finite route family, tag carriers with the route: use the disjoint union of (r,x), preparations labelled r, and tests labelled (r,y). The deterministic map (r,x)->(r,Q_r x) is the same leg-preserving construction. Route choice occurs before that fresh block. Querying two routes on ONE shared block is a different context and requires the cumulative combined query to pass its own adequacy check; separate marginal route certificates do not imply that joint law. Products and causal composition of genuinely fresh blocks then give the actual mission cylinder, with the same route labels, physical wiring and guards used by the operational proof.

This witnesses the application of the checked v2 comparison construction, rather than assuming a generic interface comparison. True S and maximal V agree only on the proved RESTRICTED external cylinder. Their raw source distributions, hidden carriers and unrestricted full-state tests need not agree. Nothing requires lifting V to the original physical filter or recovering its stationary Toeplitz presentation. A finite-H interface also does not establish an arbitrary-horizon stationary realization.

Coherence is used separately for each actual supported source law and its admitted network. Identifications across S/V are only at cylinders proved equal by the experiment criterion. At a failed confidence event no exact identification is promised; its probability is charged. No formal free-Isbell apex is thereby finite, stochastic or executable. Algebraic compact feedback does not authorize instantaneous physical feedback: the operational feedback language is guarded and unfolded over the declared finite block/time budget.

## 9. What assumption has been removed and what remains

Removed as known data: physical source grouping, number of sources, overlapping linear incidence, and exact delays/coefficient matrices within the supplied bound. Learned evidence gives a positive behavioral source/interface and a checkable extension to mission observations without recovering those details.

Still supplied: finite-field linearity, fair independent innovations, stationary coefficients across acquisition/service, the memory upper bound D, reliable physical observation, gate noninterference, source-complete hazard tests, and safe costed isolation/draining. These are substantial model-class and physical premises. The theorem is not arbitrary causal architecture discovery. Unbounded hidden delays, rare unmodelled modes, action-induced source changes, or nonlinear coupling can invalidate its completeness and safety claims.

The support-learning, dual-union criterion, route checking and testing lower bound are classical algebra/probability constructions. Their connection to the actual two-sided comparison machinery and same-source mission chain is an application/integration result. No priority claim or discharge of every retained contract obligation is made.
