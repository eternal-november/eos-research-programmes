# Witnessed common refinements and feedback composition

Proof candidate dated 29 October 2026. This note supplies a constructive operational common refinement, its restricted bridge to the actual original C5 presentation, and explicit obstructions. It does not claim that the original calculus identifies physical components or generates arbitrary operational cells.

## Main conclusions

Several predictive descriptions can be combined without replacing their shared uncertainty by independent choices. The combination must use one actual joint response witness, with positive probabilities, lawful access to current inputs, and persistent memory. A finite support search below discovers a common refinement or proves none exists in its declared witness language. The projection maps to the descriptions can be noninvertible. The same certificate works for every feedback controller using the certified reports and admitted actions, subject to the original physical regime and coverage assumptions.

A separate compiler turns each finite licensed update schedule into an actual original C5 operation after a faithful finite interface enlargement. Its ordered refinement witnesses are genuine C5 witnesses. This does not identify arbitrary crossing operational decompositions with original planar refinements. An explicit crossing obstruction is retained below.

The fixed source encodings are part of the endpoint contract, not intrinsic environmental semantics. Equal behavioral kernels can have incompatible fixed seed encodings. Permitted local source recodings must be searched when the request concerns behavior rather than those specified encodings.

## 1 Source obligations and what is new

The earlier `certificate_guided_discovery_20261029/theory/Operational_Certificate_Bridge.md` already proves that local update, delivered-interface and output equations imply persistent feedback realization. Its `Source_Derived_Residual_Certificates.md` already compiles original C5 normal forms and combines residuals on shared variables. We do not count those statements again as a new discovery theorem.

The additions here are a constructive common-response refinement search, explicit noninvertible endpoint witnesses, a faithful parameter-enlargement bridge to genuine C5 operations, and an exact distinction between ordered C5 common refinements and crossing operational covers. In the additive observed-output specialization, the common event IDs and product observer are directly constructible; the general finite common-response search explains which extra assumptions make that construction legitimate and what failure means.

## 2 The common-response witness language

Fix finite actions A and finitely many charts i. Chart i has finite memory S_i, response alphabet E_i, update table F_i:S_i×A×E_i→S_i, and report table H_i:S_i→O_i. Transition reports can be retained in the next memory state so that this convention loses no finite-state cases. Its initial memory law is μ_i and fresh response law is ν_i. Tables may have a finite persistent structural selector θ. Probability weights may range over an arbitrary specified real semialgebraic or linear uncertainty set; no finite probability grid is assumed. A single choice of θ and all weights is retained across every use and every time step.

A declared endpoint relation C_0⊆∏_i S_i records the actual agreement demanded between shared reports or memories. It does not identify merely equal-looking occurrences. Shared response IDs likewise impose an actual relation E_0⊆∏_i E_i. Any response coordinate that is genuinely shared occurs once and is projected to its users.

For the initially pinned response encodings, a common witness consists of:

* a nonempty state support C⊆C_0;
* one initial probability η on C with the specified chart marginals;
* one positive normalized probability λ on E_0 with the specified chart response marginals;
* closure F_e(c,a)=(F_i(c_i,a,e_i))_i∈C for every c∈C, a∈A, and e with λ(e)>0;
* equality of every report that the endpoint contract says is shared.

At each step draw one response tuple e with law λ, independently across time under this declared fresh-innovation model, and supply its actual projections. Do not draw independent chart responses. Neither independence across charts nor a product of overlapping marginals is assumed. A more general temporal source model must retain its source state as part of C and prove the corresponding update equations; it is not covered by relabeling a temporally dependent source as fresh.

A real probability vector in a semantic uncertainty family is not automatically an exactly executable sampler. A physically existing innovation is an assumed or calibrated environmental source; a requested simulator or deployed random generator needs a specified numeric representation and licensed sampling primitive. Rational linear feasibility with rational inputs admits rational witnesses when feasible. Dyadic probabilities can be sampled with a bounded number of fair bits; general rationals may require rejection sampling with unbounded worst-case time or a bounded approximation with charged total-variation error. Arbitrary irrational or uncomputable weights are not claimed implementable by a finite program. Source access, fanout, generation and latency costs are explicit resources, not free C5 operations.

Hidden joint memory not represented by the chart tuple is not supplied for free; add it as an explicitly bounded state coordinate and include its update/initialization constraints if that witness language is wanted. The projections p_i:C→S_i and r_i:E_0→E_i are the concrete refinement maps. They satisfy

    p_i F(c,a,e) = F_i(p_i c,a,r_i e).

They can be noninjective. This equation includes actual endpoints and the same response occurrence, not just equality of output distributions.

### Recodings are operational witnesses

For behavior-relative rather than fixed-encoding requests, add unknown permitted encoder programs R_i. Each takes a common source value and precisely the locally available current inputs, and produces the local response. Its table is shared across all calls. Source generation, communication, timing and local read permissions must be checked by the executable observer/compiler contract. The pushforward response law required by a chart must hold at every admitted local input. It is not enough that it holds at the inputs present in one recorded run.

A finite bound on source alphabet, encoder memories, gates, messages and alphabets gives a finite family of deterministic encoder tables. Enumerate those tables as structural choices, then run the common-refinement procedure for each resulting joint response map. Concretely, a common finite source alphabet E has one law λ, and the update uses F_i(c_i,a,R_i(local_i(c,a),e)). For every local input in a FIXED declared encoder input domain and response value v impose the linear row sum Σ_{e:R_i(local_i(c,a),e)=v} λ_e=ν_i(v). This input domain is fixed before support pruning, so these law constraints do not silently change when a state is deleted. The source projections r_i in the pinned version are thereby replaced by actual locally licensed encoders; no action-independent coupling of the old seed names is required. Positive source weights remain real unknowns in an LP when the marginals are fixed linear constraints. Recodings with their own memory can be absorbed into the finite joint state carrier. If response-law correctness is instead required only at the inputs reachable in an unknown retained C, enumerate C⊆C_0 as well, check closure for the chosen L, and impose the row constraints exactly on C. The greatest-invariant shortcut of Section 3 need not preserve completeness under those C-dependent law constraints: its larger invariant set may introduce additional response-law equations. The full finite (C,L,encoder) search is complete for that reachable-input variant. This search is complete only for the declared bounded encoder language. It is not complete for all behaviorally equivalent stochastic models or all physical implementations.

## 3 Discovering a common refinement rather than assuming one

For fixed deterministic response tables, enumerate subsets L⊆E_0. For each L define

    C^0_L = C_0,
    C^(n+1)_L = {c∈C^n_L : F_e(c,a)∈C^n_L for every a∈A and e∈L}.

The sequence stabilizes after at most |C_0| strict deletions. Call its limit C_L. Test two finite positive feasibility systems:

1. λ_e≥0 for e∈L, sum λ_e=1, with all prescribed response-marginal constraints; set λ_e=0 outside L.
2. η_c≥0 for c∈C_L, sum η_c=1, with all prescribed initial-law marginal constraints.

Additional coupled evidence rows use the SAME λ, η and structural tables. If those rows couple parameters, solve the systems jointly, not chart by chart. For a fixed linear uncertainty set this remains linear in the probability variables. Nonlinear statistical/model restrictions require their actual solver and are not advertised as LPs. The algorithmic claims assume explicitly represented rational linear systems, or another specified effective exact decision procedure. Arbitrary uncomputable real constants or an unevaluable uncertainty predicate supply semantic sets, not an executable solver. No numerical tolerance is silently treated as an exact positive witness.

**Theorem 1.** This finite support search succeeds exactly when a common witness of Section 2 exists. A successful row supplies all its actual noninvertible projection maps, initial coupling and joint response law.

**Proof.** At a fixed point every update under an e∈L stays in C_L. Feasible probabilities therefore give a common witness; zero-weight e in L do no harm. Conversely, let (C,η,λ) be a witness and take L=supp λ. Induction shows C⊆C^n_L: initially this is the endpoint condition; if true at n, every update of a point in C remains in C and hence in C^n_L, so its starting point survives the next deletion. Thus C⊆C_L. Extending η by zero and retaining λ satisfies the two feasibility systems. QED.

The search has an explicit finite bound of 2^|E_0| support candidates, at most |C_0| deletion rounds per candidate, and O(|C_0||A||L|) table checks per round before feasibility solving. This can be huge. In a factored implementation one instead uses the actual shared-variable constraints and width bounds; small physical neighborhoods alone do not bound the joint witness width. The theorem does not require a supplied common refinement, but does require finite chart/source/interface and implementation budgets.

If Θ has several candidate structural worlds, run the constraints with one persistent θ. Retain every feasible θ and every feasible probability vector, or explicitly choose one model only when the task asks for an existential realization. A nonempty existential result is not an all-model assurance statement. To obtain one uniform executable encoder, its program variables must be shared across θ; solving independently and deploying a θ-dependent encoder would require access to θ that has not been granted.

## 4 Feedback and uncertainty preservation

**Theorem 2.** A common witness realizes every chart transition and report under every admitted adapted action process, for every finite horizon. If a controller uses reports that each compared implementation can actually produce, the common system and each implementation give the same closed-loop transcript law. A controller may also use the joint report of the common refinement when that report is executable; this is a new composed implementation, not a claim that one chart alone exposes the other charts' reports. The guarantee is uniform over these controller languages, not only the policy used to fit the charts.

**Proof.** Couple the common system and chart i using the projected initial value and the same response tuple at every step. Assume p_i c_t=s^i_t. The commuting equation gives p_i c_(t+1)=F_i(s^i_t,a_t,r_i e_t). Conditionally on the complete past and chosen action, the projected or recoded response has law ν_i by the common fresh-source assumption and the marginal constraints at every admitted input. Hence the projected process obeys the chart's controlled kernel. For the closed-loop comparison, the full transcript used by the controller is required to be preserved, not merely its one-chart marginals. The controller then chooses the same action when coupled with the same private randomness. Induction proves the pathwise relation and equality of transcript laws. The same equations hold for every admitted action, so no fitted-policy-specific argument is used. QED.

The theorem is about candidate semantics under the stated physical intervention regime. Statistical coverage is still required for every history/action row reached by the proposed controller. If equations or learned kernels are established only on a covered domain, introduce an explicit escape event. A standard common-noise maximal-coupling induction gives the finite-horizon bound

    TV(Law_true^π, Law_model^π) ≤ δ_initial + sum_(t<H) ε_t + P_true^π(coverage escape),

when conditional one-step total variation is at most ε_t on the jointly coupled covered prefixes. Clip the right side at one. This follows by a union bound on initial mismatch, conditional next-step mismatch and the first escape. It does not make the escape probability known. A change of sensor mechanism, actuator effect, logging load or intervention regime requires its own justified transfer; C5 equalities cannot supply it.

All candidate weights and structural selectors are fixed globally before a run. The model family is {Law_(θ,p)^π:(θ,p) feasible}, not a process allowed to pick a new feasible θ or p after each action. Such rectangularization can create new behavior. For example, let each step output independent fair A,B and C=A XOR B XOR θ with θ fixed in {0,1}. Every pairwise marginal is uniform for both θ. Across two steps the parity must be the same, whereas independently choosing θ each step admits parity changes. Pairwise evidence does not authorize that temporal reselection.

## 5 Positive gluing failure and an encoding failure are different

### A genuine incompatible joint law

Consider three fresh bits A,B,C. One crossing cover specifies fair perfectly anticorrelated AB and BC. It is realized by the law assigning probability 1/2 each to 010 and 101. A second cover specifies fair perfectly anticorrelated AB and AC. It is realized by probability 1/2 each on 011 and 100. They agree on the shared AB law and every singleton marginal. Nevertheless their combined requirements have no positive joint law: A≠B and B≠C force A=C, contrary to A≠C. The common positive feasibility system is empty. Replacing the second cover's AC anticorrelation by equality admits the first common law. This is a true fixed-event probabilistic incompatibility, not lack of a convenient seed naming convention.

### Equal behavior with incompatible fixed seed encodings

Let F_1(a,e)=e and F_2(a,e')=e' XOR a, with fair seeds and common action a∈{0,1}. Both output a fair bit for each action. A single action-independent joint seed law supported on equal outputs would require e=e' at action zero and e≠e' at action one. Its support is empty. This does NOT prove behavioral incompatibility. If the second encoder can read a, the lawful recoding e'=u XOR a from one common fair u makes both outputs equal. If it cannot read a or receive it in time, that repair is unavailable in that resource type.

The exact checker `../tests/check_source_encoding.py` verifies this distinction. It also verifies the standard PR-box locality obstruction: the four positive fair-marginal laws x XOR y=a b have no mixture of deterministic local response functions x=f(a), y=g(b), while a licensed one-bit message carrying a to the second side permits x=u and y=u XOR a b. This is a familiar Bell/local-response example, not a novelty claim. Positivity and access permissions each impose a real condition. Pairwise positivity is not a common executable response witness.

### A common source is not an obstruction without resource restrictions

For finite global input set V and arbitrary positive output kernels K_v on a finite set Z, let E=Z^V and put λ(e)=∏_{v∈V}K_v(e(v)). Then λ is a probability law, and the deterministic response F(v,e)=e(v) has law K_v at every v. The proof is summation over all coordinates except v. Thus any collection of actionwise/global-state couplings can be represented by one input-independent finite source if its alphabet is unrestricted and the response function may inspect the full global input. The construction can be exponentially large and imposes an arbitrary unobserved coupling between counterfactual rows; it is not discovered causal structure.

Consequently the common-source requirement alone is not a stronger behavioral test in that unrestricted finite setting. Its nontrivial restrictions here are actual local input permissions, reuse of the same response table at equal local inputs, source/message/memory budgets, endpoint identities and dynamic compatibility. The PR example fails because local actors cannot inspect the other actor's action, while the fair-bit encoding example succeeds as soon as the required action-aware recoding is allowed.

## 6 Noninvertible endpoint certificates

Given a fixed chart with update F and report H, a proposed coarsening q:S→T has a pathwise same-source update on T iff, for each action and response, qF(s,a,e) is constant on every q-fibre. Its report descends iff H is constant on every q-fibre. Necessity is immediate from evaluating two states with equal q value. For sufficiency define the descended tables by the common values on im q; use that image as the effective state carrier, or declare arbitrary values on unreachable codomain points. This is an exact criterion for the pinned response representation, not for existence of another law-equivalent realization after recoding.

For an actual finite continuation with action and source record fixed, retain

    R_q(s_0,s_H,t_0,t_H) iff q(s_0)=t_0, q(s_H)=t_H,
                                      s_H=F^H(s_0;actions,sources).

A requested fine endpoint is certified by pinning its actual value in this relation. Coarse endpoint equality does not choose an inverse. Consecutive certificates compose by joining on the SAME intermediate fine state and persistent parameter/source IDs, then projecting only unrequested variables. Existentially discarding that fine state independently on both sides can create a spurious lift. Empty continuations retain s_0=s_H; after forgetting the fine state, equal coarse images describe a kernel pair, not equality of the forgotten endpoints.

For this gluing statement restrict to PINNED, context-independent source maps, not arbitrary input-dependent recoders. For two witnessed refinements into the same actual endpoint mechanism, require state maps p:X→Z and q:Y→Z, source maps r:E→D and s:F→D, the same endpoint update T, and the two literal equations pU(x,a,e)=T(px,a,re) and qV(y,a,f)=T(qy,a,sf). Require the two initial laws to have the SAME pushforward on Z and the two fresh source laws to have the SAME pushforward on D. Initialization is independent of the fresh source stream, and each stream is iid under this model. The state fibre product {(x,y):px=qy} and source fibre product {(e,f):re=sf} are then closed under coordinatewise transition by the displayed equations. Matching these full endpoint laws admits a positive initial coupling and a positive source coupling, for example the conditional-product gluing on each positive-mass endpoint fibre. Explicitly, if the two source laws are ν_E,ν_F with common pushforward ν_D, set λ(e,f)=ν_E(e)ν_F(f)/ν_D(r(e)) when r(e)=s(f) and ν_D(r(e))>0, and zero otherwise. Summing over f with s(f)=r(e) recovers ν_E(e); zero-mass fibres carry no mass on either side. The other marginal and the analogous initial coupling follow identically. Closure follows because both projected next states equal T(px,a,re). Thus independently repeating this joint source and using the coupled initial law constructs the claimed process. That gives one compatible model, not evidence that conditional independence is physically true. Retain all feasible couplings when that correlation is uncertain. A cycle of several partial endpoint requirements may have empty joint feasible set, as above. For input-dependent recoders, fibrewise gluing separately at each input is not enough: one common source law and lawful local response programs must again be solved jointly across inputs.

## 7 A genuine original C5 compiler with a stated limit

Let K be the original finite interface category and M its original finite commutative scalar monoid. Use its regular faithful finite-set realization F, as recorded in `original_mixed_criterion_20261029/references/contract/structural_extracted/GraphSpanModel.md` Section 6. Enlarge the finite collection of interfaces by the finite named bundles needed by a selected licensed circuit. Let K′ contain all functions between those finite tagged carriers; include persistent finite structural selectors as retained coordinates and restrict operational maps to preserve them. If Θ is nonempty, the old embedding sends f to id_Θ×F(f) and is faithful. Real probability weights are annotations on the common finite source alphabet, not new finitely quantized states of K′. The compiled operations use scalar 1 in the original M; source probabilities are not silently reinterpreted as C5 scalar labels.

Unroll one update schedule in phase order. Condition on one actual joint source value supplied at a named external innovation port. Source exposure, delivered messages, old-memory reads, scoped table evaluations, source projections, additions, observer updates and final record/commit are actual named vertices of a finite graph G. Each circuit stage is a function f_j:A_(j−1)→A_j between available-wire bundles. Retain side inputs explicitly until their final use. The last projection/commit is a real licensed stage. The stochastic draw is not falsely treated as a deterministic finite function: its positive law and freshness certificate annotate the external source port; C5 compiles the conditional deterministic circuit. Each stage reads only its permitted wires; this requirement comes from the operational certificate, not from the abstract finite-function category.

For any selected sequential stage grouping U_1,…,U_n, retain the complete path of actual composed arrows g_1,…,g_n and its composite g. The tuple

    (G; U_1,…,U_n; g_1,…,g_n; 1)

is an original C5 FlatCut operation in C(N′,K′,M), where N′ admits |G|. The original right-comb compiler constructs its syntax from exactly the old C, U and D generators. Refining one stage by its actual substage sequence gives the original occurrence-wise refinement, with increasing embeddings and full intermediate interfaces. The seven original rules preserve the same graph partition, arrow path composite and scalar as proved by the original normal-form theorem. They therefore preserve this compiled update denotation. Normalizing the C5 syntax does not erase the attached operational witness store. If an internal source/table/memory/endpoint is named by another request, it remains retained with its equations; an old equation is not permission to discard an observed factor witness or resample it. The faithful K→K′ embedding and N inclusion reflect equality on old full original profiles: old partitions, arrows and scalars are retained literally.

This is a conservative parameter enlargement plus an operational certificate over genuine C5 operations. It is not a proof that old K already contains these runtime arrows; that old original graph vertices were physical state coordinates; arbitrary finite spans or operational cells are generated by the original ordinary envelope; or hardware access/cost follows from the arrow denotation. A tape-retaining encoding alone would be vacuous about locality. Here its substantive premises are the already checked local read permissions, shared response IDs, positive joint source witness and persistent memory equations. The compiler records their actual composition; it does not manufacture those premises.

### Crossing operational covers need not have a common original refinement

Suppose two ordered original partitions U_1,…,U_m and V_1,…,V_n have a common original refinement. If U_i∩V_j and U_(i′)∩V_(j′) are nonempty with i<i′, then it is impossible that j>j′. Indeed, take a vertex in each intersection. Their common refined occurrences must appear in increasing order for the U run decomposition and decreasing order for the V run decomposition, a contradiction. Empty occurrences and scalar labels do not remove it.

For graph-only partitions with identity arrows and scalar one, absence of such inversions is also sufficient: list the nonempty intersection atoms in their common product order. They refine both partitions, with their induced graphs. With general arrows, the actual shared atom-arrow factors and full intermediate interfaces must additionally exist; their finite source compiler decides that condition.

Thus {0,1}|{2,3} and {0,2}|{1,3} have no common original ordered refinement. They may nevertheless be valid crossing ownership views of one synchronous operational network. In the additive observed-output theorem, intersections of ownership blocks and the synchronized product observer construct a JOINT operational refinement, retaining every original innovation event (t,B) and charging union interfaces/memory. Calling it a common original C5 refinement would be false unless its full ordered profiles also pass the source condition. A swap or interchange extension, or a different explicitly proved diagram language, would be required for unrestricted crossing source refinements.

## 8 Additive observed-output specialization

The companion discovery theorem uses outputs Y_i=f_i(scoped history,current action)+E_i. A discovered innovation block B provides ONE event ID (t,B) with joint law ν_B. Every ownership component receives the appropriate projection of that same event. Product factorization is between the justified blocks B, not between arbitrary ownership pieces. Splitting an ownership block therefore does not resample its innovation.

Each local predictor memory is a stable Moore quotient of the actual scoped suffix-shift machine. Given two such representations, the product of their memory maps on the union stream is executable and recursively closed wherever both update/output certificates apply. It is a noninvertible common refinement through the two projections; its reachable image, not the entire Cartesian product of independently chosen states, is the admitted state carrier. Candidate crossing ownership partitions refine by their intersections while shared source event IDs remain unchanged. Any additional messages, larger memory or source fanout must pass the actual implementation budget.

The C5 stage compiler applies directly to delivered-symbol reads, local quotient updates, f_i evaluation, the shared E_B projections, addition and recording. This establishes a source-grounded composition certificate for the discovered family, while the operational product construction and all-action equations establish reuse under feedback. Coverage and physical regime remain independent obligations. Nothing here proves universal hidden-state architecture identification or discovery outside the declared additive/source and observable-dictionary assumptions.

## Reproduction

`../tests/check_witnessed_feedback.py` uses exact rational arithmetic and basic-feasible-support enumeration for its small positive marginal systems, with no probability grid. It checks the incompatible triangle and repair, fixed-seed support failure and recoded feedback, persistent versus resampled parity, 5,804 ordered-partition pairs for the C5 crossing criterion, and conditional update equality under two owner schedules with one shared source tuple. `../tests/check_source_encoding.py` independently checks the encoding/locality examples. These finite checks support the displayed general proofs; they are not a proof by bounded enumeration.
