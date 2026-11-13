# A constructive hidden-correlation path theorem

## Useful result first

**Reading guide:** Section 9 is the strongest theorem: heterogeneous transition and emission kernels, recovered from local moments over three ticks with nonrecursive finite-sample conditioning. Sections 1–8 prove and check its homogeneous special case.

There is a growing class with **unknown component pairing, unknown path order, unknown positive noise kernels, no revealing actions, and completely uninformative one-time readouts** in which degree-at-most-six, two-time moments discover the components, their persistent one-bit shared interfaces, port alignment, and positive local mechanisms. Search/checking are polynomial in the number of visible ports; the joint predictive rank is exponential. This is a scoped exact theorem, not a general positive-realization theorem or a novelty claim. It avoids reconstructing the global hidden state frame altogether.

The same example gives a genuine crossing-decomposition warning: grouping ports into their discovered pairs admits bounded local memory and one-bit nearest-neighbor messages, whereas each of the two crossing streams individually is iid and nevertheless their joint realization requires at least k persistent bits in total. Marginal autonomous summaries do not certify a compatible joint implementation.

## 1. Fixed model universe, not supplied instance

Fix k>=2. There are 2k **named observed binary ports**, but their partition into k pairs and the ordering of the pairs along a directed path are unknown. A model has hidden bits C_1,...,C_k and independent fresh noises at each tick:

- C initially uniform on {0,1}^k;
- C'_1=C_1 XOR E_1;
- C'_i=C_i XOR C_{i-1} XOR E_i for i>1;
- E_i are Bernoulli(epsilon), common unknown 0<epsilon<1/2;
- pair i outputs Y_i=A_i XOR N_i and Z_i=A_i XOR C_i XOR M_i;
- A_i are fair bits; N_i,M_i are Bernoulli(eta), common unknown 0<eta<1/2.

All fresh variables are mutually independent and independent of past state. The assignment of the named ports to Y_i,Z_i and i is not given. Define rho=1-2eta and tau=1-2epsilon. We deliberately fix the *grammar* (path, two ports per cell, XOR stochastic mechanism); we do not supply its partition, frame, alignment, kernels, or parameters. This is more restrictive than arbitrary finite-rank positive realization. The unknown model is not a finite list of templates with known numerical parameters.

There are no actions in this theorem. It is an uncontrolled subclass of action/readout histories, not a claim about unknown general action targets. The user does not observe C, A, E, N or M.

The deterministic triangular XOR map on C is a bijection. Product binary noise is doubly stochastic. Consequently uniform C is stationary. At each single time all 2k observed bits are jointly uniform: even the correct pairing is invisible in the complete one-time distribution. Every finite readout has positive probability, and no finite observation history reveals C exactly. Interacting dynamics are nontrivial for every nonroot cell.

## 2. Discovery theorem

For an observed port set S, let chi_S(o)=(-1)^(sum of its bits). For every candidate future pair Q of named ports and every past set S of size 2 or 4, obtain

    m(S,Q)=E[chi_S(O_t) chi_Q(O_{t+1})].

There are O(k^6) entries; each requires only two consecutive noisy observations and involves at most six bits.

**Theorem.** In the universe above:

1. A candidate pair Q belongs to the true component pairing iff at least one m(S,Q) is nonzero.
2. Every recovered pair Q_i has exactly one such nonzero entry. For the root its past set is S=Q_i. For each nonroot it is S=Q_i union Q_parent(i).
3. Thus pairing, root, predecessor map and complete directed path are discovered without latent-coordinate recovery or template enumeration.
4. All root entries equal a=rho^4 tau, and all nonroot entries equal b=rho^6 tau. Therefore

       rho=sqrt(b/a), eta=(1-rho)/2,
       tau=a^3/b^2, epsilon=(1-tau)/2.

   The strictly positive local transition and emission kernels are thereby constructed.
5. Swapping the two ports within any recovered pair is an unresolved gauge; retain all such swaps or their equivalence class. The procedure does not invent a preferred physical labeling.

**Proof.** A future candidate pair drawn from different true cells contains two independent fresh fair A variables, each appearing once. Its conditional expectation given the entire past and C at both times is zero. Therefore every tested moment vanishes.

For a true future pair Q_i the A variable cancels. Its conditional sign expectation is rho^2(-1)^(C'_i). Similarly a past monomial has zero expectation conditional on C unless its port set is a union of complete true pairs. If S is a union of pairs indexed by T, its conditional expectation is rho^(2|T|) chi_T(C). Write F for the invertible binary triangular path matrix. Uniformity of C and orthogonality of binary characters give

    m(S,Q_i)=rho^(2|T|+2) tau * 1{T = support(F^T e_i)}.

For the root this support is {i}; otherwise it is {i,parent(i)}. All indicated coefficients are strictly positive. This proves every assertion, including parameter formulas. Pair swaps simply redefine the fair A by A XOR C, which has the same fresh uniform conditional law. QED.

This is an algebraic low-order reconstruction theorem, not a premise that suitable local statistics already exist. The distinguishing moments themselves recover where the unknown shared state lives.

## 3. Positive realization and persistent interface

For each recovered pair create a component storing one bit s_i. Set its initialization to an independent fair bit. It owns the discovered pair of readout ports and samples their joint kernel

    L_i(y,z | s) = [1 + rho^2 (-1)^(y+z+s)] / 4.

This kernel is strictly positive and normalized. Its two individual output marginals are fair. It must be sampled **jointly**: replacing it by the product of its marginals loses the entire persistent correlation mechanism.

At a synchronous tick:

1. Emit the pair jointly from L_i(.|s_i), using fresh independent local randomness.
2. Send the old stored bit s_i to the successor, if any.
3. Sample E_i independently and update s'_i=s_i XOR incoming_bit XOR E_i, with incoming_bit=0 at the root.
4. Commit all new bits after the old-bit messages have been read.

The interface is recursively maintainable, causally available and persistent; it is not a statistic of an inaccessible full observation history. Initialization, owned output sampling and aliasing are explicit. Induction on ticks proves equality of every finite joint readout law with the discovered model. No global broadcast, global state copying, extra delay line or shared random seed is used.

**Resource ledger.** There are k persistent bits, k-1 one-bit messages per tick, one neighbor-message dependency per nonroot, and one synchronous read/update barrier. Each component has two readout ports, one bit of local state, and a constant-size kernel. Sampling an exact irrational Bernoulli is an idealized stochastic primitive; rational implementation and approximate kernels must charge precision/randomness explicitly. Parameters and port lists have O(k) description length besides real-number precision. The discovery moment table is O(k^6), not O(2^k), and scanning it is polynomial. The complete model-family membership claim cannot be certified from those moments for an arbitrary external process: sufficiency uses the declared universe.

## 4. Exponential global rank and optimality of persistent memory

Let O be all 2k readouts and let E(o,c)=P(O=o|C=c). For every subset T of cells,

    E[ product_(i in T) (-1)^(Y_i+Z_i) | C=c ]
        =rho^(2|T|) chi_T(c).

The binary character matrix is invertible and every multiplier is nonzero. Hence E has column rank 2^k. The hidden transition matrix K is invertible: it is a permutation matrix followed by a tensor product of invertible binary-noise matrices (eigenvalues 1,tau). With uniform full-support initialization, the adjacent-observation probability matrix is

    P(O_t=o,O_(t+1)=o') = [E diag(mu) K^T E^T]_(o,o'),

and has rank 2^k. Thus the full predictive/Hankel rank is exactly 2^k: the displayed finite submatrix gives the lower bound, and the constructed 2^k-state HMM gives the upper bound.

Any finite-state causal stochastic realization with fresh randomness independent across ticks and total persistent joint state alphabet R has such a past/future matrix of rank at most |R|. Therefore |R|>=2^k, or at least k persistent bits. Distributed implementations count the joint alphabet of all private and shared persistent stores; preloaded random tapes, correlated persistent seeds, pending messages and delayed events are not free. The constructed local realization attains this total-memory lower bound while avoiding exponential computational representation during discovery.

This is a genuine improvement over *explicit* global spectral-HMM reconstruction (which must represent rank 2^k), not a theorem that no other structured learning algorithm can match it.

## 5. Crossing decomposition and the correct obstruction

Choose one port from each discovered pair for stream Y, and put the other ports in stream Z. For k>=2 the pair scopes Q_i cross the two stream scopes: neither family refines the other. Each whole stream, by itself, is iid uniform over k-bit symbols. Its predictive rank is 1 and it needs zero temporal state.

Their joint process nevertheless has rank 2^k. Consequently independently realizing their zero-memory marginal models cannot be glued into the observed joint model without restoring at least k bits of persistent state somewhere. If both stream components are required to retain zero private temporal state, their persistent shared interface must have at least 2^k states. Allowing private state reallocates, but does not remove, the k-bit total lower bound. Fresh within-tick shared randomness alone does not evade the rank bound.

A compatible crossing realization *does* exist using the k-bit vector C as a shared persistent record, with the local pair-factor schedule above. It is exactly the same state once, not two resampled copies. This gives an explicit crossing transport with the measured cost: bounded pairwise interfaces become an unbounded-width stream interface. It does not establish a general nonlaminar calculus theorem or that arbitrary crossing decompositions preserve finite budgets.

## 6. Honest finite-data extension

Use n independent stationary two-tick episodes; do not pretend adjacent samples from one dependent run are independent. Let M be the number of tested entries and h=sqrt(2 log(2M/delta)/n). Hoeffding and a union bound give simultaneous moment error <=h with probability >=1-delta.

If rho>=rho_0>0 and tau>=tau_0>0 are declared margin bounds, every nonzero tested moment is at least g=rho_0^6 tau_0. When h<g/2, threshold at g/2 recovers the exact pairing and path. Retain the entire parameter set satisfying rho,tau in the declared bounds and

    |rho^4 tau - a_hat|<=h,
    |rho^6 tau - b_hat|<=h

for all relevant measured root/nonroot entries. It contains the truth on the same event. This is a two-parameter confidence set *after constructive discrete discovery*, not semialgebraic architecture search. At exact moments the set is a singleton.

For two retained parameter points, a direct coupling of the hidden innovations and the two local readout noises gives, for H ticks,

    TV(law_H, law'_H) <= min(1, k(H-1)|epsilon-epsilon'| + 2kH|eta-eta'|).

Use the shared fair initialization and A variables and maximal couplings of each Bernoulli noise. A union bound over discrepant innovations proves the claim. Thus uncertainty can be propagated to any finite requested horizon; approximate parameters do not imply a uniform-in-infinite-time error bound. Without a positive margin no finite sample count guarantees exact pairing uniformly near eta=1/2 or epsilon=1/2.

## 7. What remains open

- In Sections 1–8 the grammar is a hidden binary parity path with homogeneous noise; Section 9 removes homogeneity. Arbitrary local mechanism forms, arbitrary action targets, tensor factors and invariant cones remain unsolved.
- The local state is synthesized from a specific low-order moment signature, not from an arbitrary finite-rank predictive representation. The general algebraic positive-realization problem is not closed.
- The theorem gives a common growing noisy family linking discovery, positive assembly, finite memory/communication and finite-data confidence. It does not satisfy every wider contract obligation or establish literature priority.
- The crossing result supplies a constructive alias-preserving realization and a necessary resource blowup. It does not show a general reusable crossing-certificate advantage over all structured baselines.

The heterogeneous-noise identifiability question raised by this original special case is resolved constructively in Section 9. Unknown bounded-degree invertible binary-linear dynamics remain a separate generalization.

## 8. Checks and independent review

`check_constructive_target.py` checked the entire indicated two-time moment table, uniform one-time law, parameter inversion, marginal stream temporal independence and ranks 4,8,16 for k=2,3,4. Maximum floating-point moment discrepancy was below 2e-16. A separate exact-rational k=2 check verified rank four and uniform marginals. These bounded checks support, but do not replace, the all-size proof. Results are in `Constructive_Target_QA.json` (the exact-rational check is reported by the script).

The independent target-fidelity reviewer found no mathematical blocker in the proof and confirmed genuine discovery of the unknown grouping/order/kernels. The reviewer emphasized three scope limitations: the fixed homogeneous XOR-path grammar; the reconstructed state is a correlation bit rather than compression of a richer source; and the stream crossing requires width k, not a simultaneous constant-width crossing realization. Independent stationary episodes are a declared experimental resource, not a substitute for a single-run mixing theorem.

# 9. Main upgrade: heterogeneous kernels, locally conditioned identification

**This extension removes the homogeneous two-parameter restriction of Sections 1–6. It is the stronger result.** The earlier theorem is a transparent special case. The broad unknown-sparse-mixed-AR/ compressed-port theorem in `Coupled_Family.md` is separate; this family contributes discovery of a persistent correlation mechanism that every separate crossing view erases completely.

## 9.1 Expanded fixed universe

Retain the unknown port pairing, unknown directed path and uniformly initialized hidden bits. Each hidden transition has its own unknown bias tau_i in (0,1), with P(E_i=1)=(1-tau_i)/2. The two readout noises for cell i may have different unknown rates eta_i,Y and eta_i,Z in (0,1/2). Only

    r_i=(1-2eta_i,Y)(1-2eta_i,Z) in (0,1)

is identifiable from the observed process. Its joint emission kernel is

    L_i(y,z|s)=[1+r_i(-1)^(y+z+s)]/4.

Retain **all** sensor-noise pairs giving the recovered r_i; do not claim to distinguish them. A canonical implementation may use equal rates (1-sqrt(r_i))/2, or sample L_i directly. Within-pair orientation remains unresolved as before. Heterogeneous kernels preserve uniform stationarity, strict positivity and all nonrevealing properties.

## 9.2 Discovery and direct parameter identification

The support proof of Section 2 is unchanged. For a true pair Q_i its unique nonzero two-time moment now is

    a_i = tau_i r_i^2 r_parent(i),

where r_parent=1 at the root. Thus the same O(k^6) degree-at-most-six moment scan recovers every pair and path edge. Equal amplitudes across cells are not needed.

Write W_i,t=(-1)^(Y_i,t+Z_i,t), and set

    R_i,t=W_i,t W_i,t-1 W_parent(i),t-1,

omitting the parent factor at the root. After pairing/path discovery, obtain one extra local three-time moment per cell,

    c_i=E[R_i,t R_i,t+1].

**Heterogeneous identification theorem.**

    c_i=tau_i^2 r_i^2 r_parent(i)^2,
    r_i=a_i/sqrt(c_i),
    tau_i=c_i/(a_i r_parent(i)).

These formulas construct every local positive kernel. They identify r_i independently of the parent parameters; only the final tau_i formula uses the separately identified r_parent. In particular there is no recursive error multiplication down the path.

**Proof.** In sign coordinates write W_i,t=X_i,t D_i,t, where X_i,t=(-1)^C_i,t and D_i,t is the product of the two independent sensor-noise signs, of mean r_i. The hidden dynamics imply

    R_i,t = F_i,t-1 D_i,t D_i,t-1 D_parent(i),t-1,

where F_i,t-1 is the independent transition-noise sign, of mean tau_i. The product of two adjacent residuals cancels D_i,t exactly, leaving two independent F signs, two distinct-time D_i signs, and two distinct-time parent D signs. Their expectation is the displayed c_i. All indicated variables are independent; there is no hidden-state conditioning inference in this calculation. Substitution proves the inversion formulas. QED.

At a nonroot the observed product simplifies to

    R_i,t R_i,t+1
      =W_i,t-1 W_parent,t-1 W_parent,t W_i,t+1.

It therefore involves at most eight observed bits over three ticks. At the root it is only W_i,t-1 W_i,t+1. No latent observations or interventions are needed.

## 9.3 Positive assembly, crossing and resource optimality

Use the exact schedule of Section 3, with the discovered heterogeneous L_i and transition biases. Every finite readout law is preserved by the same induction. Each component still stores one bit and transmits one old-state bit to its successor. Fresh joint output randomness must remain jointly sampled.

In Section 4, the emission character multiplier becomes product_(i in T) r_i and the transition noise matrix has nonzero Walsh eigenvalues product_(i in T) tau_i. Thus both full-column-rank and invertibility proofs survive verbatim: joint predictive rank is 2^k, every finite-state realization has at least k total persistent bits, and the inferred distributed model attains that bound. The crossing marginal streams remain iid and require zero separate temporal memory; their joint persistent-memory requirement remains k bits. This is total-memory optimality, not an interface-only bound when uncharged private state is permitted.

## 9.4 Finite samples, including data-selected residuals

Assume independent three-tick episodes started in the declared stationary law. This is an experimental resource premise, not access to the initial hidden state. Declare margins r_i>=r_0>0 and tau_i>=tau_0>0.

To avoid a post-selection error, build a uniform confidence event for:

- all O(k^6) Section 2 candidate moments using the first two times;
- every candidate root moment chi_Q(O_0)chi_Q(O_2);
- every ordered candidate pair (Q,P) residual moment

      chi_Q(O_0)chi_P(O_0)chi_P(O_1)chi_Q(O_2).

The last family has O(k^4) members, so the total M remains O(k^6). Products with repeated ports cancel; every random variable is bounded in [-1,1]. With n episodes, set

    h=sqrt(2 log(2M/delta)/n).

All moment errors are at most h simultaneously with probability at least 1-delta. Every nonzero support moment is at least

    g=tau_0 r_0^3.

When h<g/2, threshold g/2 gives exact discrete pairing and path. This requires n>8 g^(-2) log(2M/delta), logarithmic in k for fixed margins; evaluating the requested moment table costs O(n k^6) with a direct implementation.

For numerical uncertainty, retain all local kernel parameters in the declared margins satisfying

    |a_hat_i-tau_i r_i^2 r_parent|<=h,
    |c_hat_i-tau_i^2 r_i^2 r_parent^2|<=h

for every recovered cell. The truth is retained on the same simultaneous event. Parameter alternatives and unresolved individual sensor-noise splittings are preserved. This confidence construction is downstream of the direct structural theorem, not architecture feasibility search.

There is also an explicit nonrecursive stability bound. For any two retained parameter points, let

    a_min=tau_0 r_0^3, c_min=tau_0^2 r_0^4,
    L_r=3/(r_0 c_min),
    L_tau=2/(a_min r_0)+2/(a_min^2 r_0)+L_r/(a_min r_0^2).

Then |r_i-r'_i|<=L_r h and |tau_i-tau'_i|<=L_tau h for every i. To verify: the two feasible a values differ by <=2h, as do the c values. Since r_i^2=a_i^2/c_i, subtraction gives |r_i^2-r_i'^2|<=6h/c_min; divide by r_i+r'_i>=2r_0. Apply ordinary product/reciprocal bounds to tau_i=c_i/(a_i r_parent), with c_i<=1, to obtain L_tau. Root estimates obey the same conservative bound by taking its absent parent as 1. The constants depend on margins, not path length.

A maximal coupling of each local emission kernel and transition innovation gives the horizon-H bound

    TV(law_H,law'_H)
      <= min(1, (H/2) sum_i |r_i-r'_i|
                  + ((H-1)/2) sum_i |tau_i-tau'_i|)
      <= min(1, (k h/2)[H L_r+(H-1)L_tau]).

Indeed local emission TV is |r_i-r'_i|/2 and transition Bernoulli TV is |tau_i-tau'_i|/2. Couple the same initialization and stop at the first discrepancy. This proves a polynomial sample/error guarantee in k,H and the inverse margins, without recursive exponential conditioning. No infinite-horizon approximation claim follows.

## 9.5 Scope after the upgrade

Homogeneous noise is no longer required. What remains restrictive is the binary parity-path mechanism and independent local noise, not supplied numerical kernels. We still do not solve arbitrary positive operator realization, arbitrary local transition functions, unknown general actions or simultaneous constant-width realization of both crossing decompositions. A richer source-state compression theorem is supplied separately, if established, by the broader family work. This theorem should be presented as a complementary, fully worked noisy discovery result rather than the complete general programme.

Heterogeneous regression: `check_heterogeneous_pair_path.py` independently contracts the full hidden transition matrix over three times for k=2 through 7, verifies the residual moment identities and recovers every heterogeneous parameter with error below 2e-16. These numerical regressions are recorded in `Heterogeneous_Pair_Path_QA.json`; they complement the all-size algebraic proof.

Independent review of Section 9 also approved the heterogeneous residual identities, data-selected-moment confidence event, nonrecursive stability constants and horizon-TV bound; no mathematical blocker was found.
