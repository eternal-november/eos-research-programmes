# Countable excursion interfaces: progress, wiring, and two-sided comparison

Derivation, 2026-10-31. Scoped result; not a completed general realization contract.

## Target and prior baseline

The previous qualitative quotient records support and whether local mass is missing. It cannot distinguish upward- and downward-biased walks on the positive integers; their feedback termination differs. The target here is stronger operational information on countable modules that (a) proves progress of a wired system, rather than assuming its termination, and (b) remains a meaningful statement through the actual reconstruction comparison.

Ranking-supermartingale and small-gain arguments are established baseline machinery, not claimed novelty. This note's specific bridge is numerical progress-test invariance of a genuine enriched cylinder, followed by an independently proved operational wiring theorem. Formal CFS arrows are never interpreted as stochastic maps. This does not construct an executable canonical Isbell apex.

## 1. Operational invocation interface

Wiring here is serial first-exit invocation wiring: one module executes until return or mission completion, then the next module begins. T is the accumulated internal-step cost, not a concurrent wall-clock claim. Arbitrary mid-invocation interventions or concurrent interference are outside this interface unless their effects have already been included in its conditional guarantees. There are finitely many module modes i in I. Mode i has a countable entry space X_i and an explicit potential v_i:X_i->[1,infinity). An invocation started at x executes internal steps for a positive integer duration tau and, if it finishes, either ends the mission or returns a next entry (j,y). Allow tau=infinity for local nontermination. Its operational law is an actual normalized probability kernel in x on finite stopped paths together with a distinguished nontermination outcome infinity; no conditioning on successful completion is permitted. Internal state spaces and entry spaces may both be infinite.

Crucial operational condition: conditional on the complete past and the present entry (i,x), the next invocation obeys the stated entry-kernel, or at least the bounds below uniformly. A fresh randomized implementation initialized by x is sufficient. If persistent shared randomness or hidden state influences future calls, it must be included in the entry interface or covered by uniform conditional bounds. Isolated marginal tests do not imply this condition.

Local certificates are numbers g_ij>=0 and functions b_i:N->[0,infinity), b_i(t)->0, such that for every entry x:

    E_x[1_{next mode=j} v_j(Y)] <= g_ij v_i(x),                (1)
    P_x[tau>t] <= b_i(t) v_i(x).                              (2)

Terminal exits and the nontermination outcome contribute zero to (1). Equation (2) DERIVES local almost-sure termination: P_x[tau=infinity]=lim_t P_x[tau>t]<=v_i(x)lim_t b_i(t)=0. No finite expected duration is required. Optionally retain c_i>=0 with E_x tau <= c_i v_i(x).

Every inequality is also required conditionally at an invocation boundary in the actual wired execution, as explained above. This is a local composable interface contract, not global termination.

## 2. Wiring theorem and proof

Let G=(g_ij). Suppose a finite vector w with strictly positive entries and rho<1 satisfies Gw<=rho w componentwise. Let w_min=min_i w_i, Phi(i,x)=w_i v_i(x), and Phi_0=w_i v_i(x) at the initial entry. Let N be the number of invocations before terminal exit, T their total duration; T=infinity on nontermination.

Then, for every integer m>=0,

    P[N>m] <= rho^m Phi_0 / w_min.                           (3)

For m>=1,t>=0 integer and b(t)=max_i b_i(t),

    P[T>m t] <= Phi_0/w_min *
                 (rho^m + b(t)(1-rho^m)/(1-rho)).             (4)

In particular T is finite almost surely: first choose m to make the first term arbitrarily small, then t for the second. This does not assume a uniform finite physical-step drift or finite E T.

Proof. Set Phi_k=0 after termination and otherwise equal to the weighted potential at entry k, with entry0 initial. Conditional contract (1) and Gw<=rho w give E[Phi_(k+1)|past]<=rho Phi_k. Induction yields E Phi_k<=rho^k Phi_0. On {N>k}, Phi_k>=w_min; Markov's inequality gives (3). If N<=m and each active invocation k<m has tau_k<=t, then T<=mt. The union bound and conditional (2) give

    P[T>mt] <= P[N>m] + sum_(k<m) E[1_{N>k} b_i(t)v_i(X_k)]
             <= rho^m Phi_0/w_min + b(t)/w_min sum_(k<m) rho^k Phi_0.

This proves (4). The proof also applies to history-dependent choice among implementations whose conditional bounds share the same G and b. It does not permit arbitrary changing gain matrices with individually small spectral radii: a common weight inequality is required.

If expected-duration constants c_i are present, Tonelli gives

    E T <= [max_i c_i/w_i] Phi_0/(1-rho).                     (5)

For one fixed G with spectral radius<1, a sharper bound is

    E_(i,x) T <= [(I-G)^(-1)c]_i v_i(x).                      (6)

Indeed expected accumulated reward through k remaining calls is bounded by [sum_(l<k)G^l c]_i v_i(x), by induction. Monotone convergence yields (6). Nonnegative finite G with spectral radius<1 admits positive w, e.g. w=(I-G)^(-1)1 and rho=max_i(1-1/w_i)<1 (rho=0 is allowed). Thus the final small-gain check is finite despite countable operational states.

These are sufficient certificates, not a complete characterization of termination, and (5)/(6) concern expected duration only when the optional local finite-mean contract is supplied.

## 2A. Stronger separation: invocation progress need not contract duration potential

The previous one-potential condition is sufficient but unnecessarily excludes useful almost-sure cases. Retain a SECOND local matrix P=(p_ij) with

    P_x[next mode=j | complete past, entry (i,x)] <= p_ij,

alongside (1),(2). Suppose only spectral radius(P)<1; G may have spectral radius>=1. All entries of G remain finite. Then

    P_(i,x)[N>m] <= (P^m 1)_i,
    P_(i,x)[T>mt] <= (P^m 1)_i
                        + v_i(x) [sum_(k=0)^(m-1) G^k b(t)]_i,       (7)

where b(t) is now the column vector of local tail bounds. Proof: the expected active entry-potential vector after k invocations is componentwise bounded by v_i(x)e_i G^k, by conditional (1); the same argument with constants1 and P gives the survival bound. Union-bound the first m invocation durations as before. For each FIXED m the finite sum in (7) tends to0 as t tends to infinity. Since P^m1 tends to0, first choosing m then t proves almost-sure completion. Neither contraction of G nor finite expected duration was assumed.

This is stronger in the precise required direction: the countable system can amplify the size/duration of later invocations while nonetheless terminating almost surely. Quantitative finite-horizon bounds remain explicit in (7). Finite expected-duration constants c and spectral radius(G)<1 still supply (6), but their failure does not defeat the almost-sure theorem.

To transport this richer certificate through section4, add the bounded test rows M_j(h)=1_{h returns to j}. Their preparation evaluations are exactly the entries bounded by p_ij. Only finitely many extra tests are needed.

## 3. Explicit infinite family

An entry is a positive integer n. Internally retain n and run a nearest-neighbor walk k started at n until k=0. At each k>0 move down with p_i>=1/2 and up with 1-p_i. After hitting zero, independently return to mode j at a_i n with probability r_i, or finish otherwise; a_i is a positive integer. The duration includes the walk steps; terminal decision can be made at the last step without an extra time charge. The internal state (n,k) is countable and unbounded. Use v_i(n)=n.

The unbiased walk p_i=1/2 has almost-sure finite hitting time but infinite mean. Reflection of paths at the first hit of zero gives

    P_n[tau>t] <= n max_k P[S_t=k] <= sqrt(2) n/sqrt(t+1),

where S_t is a simple symmetric walk from0. The first inequality follows by cancellation of reflected endpoint masses; the remaining interval contains n parity-compatible endpoints. The last elementary central-binomial bound is deliberately loose. Consequently b_i(t)=sqrt(2)/sqrt(t+1) is a valid local certificate. A monotone common-uniform coupling bounds any downward-biased walk by this unbiased hitting time, so the same tail bound applies for p_i>=1/2.

For p_i>1/2, let d_i=2p_i-1. Stopping the drift identity at tau wedge t gives E(tau wedge t)<=n/d_i, hence finite E tau. Wald's identity for bounded independent increments and integrable stopping time then gives E tau=n/d_i. Thus c_i=1/d_i is valid. For p_i=1/2, finite E tau would by the same Wald identity imply E S_tau=n, contradicting S_tau=0; hence its mean is infinite.

The exit-potential gain is exactly g_ij=r_i a_i. In a two-mode alternation take a_A=a_B=2, r_A=3/4, r_B=1/5. Then

    G = [[0, 3/2], [2/5, 0]],  spectral radius=sqrt(3/5)<1.

Module A alone amplifies expected potential. Its coupling to B nevertheless proves global progress. Weights w=(2,1), rho=4/5 suffice. If both p_i=2/3 then c=(3,3), and (6) is exact: E_(A,n) T=75n/4. If both p_i=1/2, (4) still proves almost-sure completion although E T=infinity. Thus this result does not reduce to a globally assumed bounded expected-time regime.

## 4. The actual enriched cylinder and its comparison

Use the small skeleton of countable sets and matrices over extended nonnegative reals, with nonnegative countable-sum composition and 0*infinity=0. Tonelli supplies associativity. This is an ambient observation category, NOT a claim that all its matrices are stochastic implementations.

For module i let H_i be its countable set of finite stopped paths, with terminal/return label, duration, and exit state, augmented by one nontermination outcome infinity. The actual UNCONDITIONAL operational law gives a normalized stochastic preparation column P_x on H_i, including any nontermination mass. Assign duration(infinity)=infinity. Include these actual test rows:

- L_j(h)=1_{h returns to j}v_j(exit(h)), with L_j(infinity)=0;
- D_t(h)=1_{duration(h)>t}, for every t in N, with D_t(infinity)=1;
- optionally C(h)=duration(h), with C(infinity)=infinity;
- the unit-mass row U(h)=1, including U(infinity)=1, so U P_x=1 is a named normalization observation;
- optionally exit indicators and any functionality tests needed by the mission.

The cylinder entries are the scalar morphisms L_j P_x, D_t P_x, C P_x. These are exactly the quantities in (1),(2),(5). Values can be infinite in the ambient category, although the certified rows have the stated finite bounds. No full stopped-path distribution need be retained as an interface test family: the named potential and tail tests suffice for this progress conclusion. They do NOT determine the joint duration/exit law or exact total runtime distribution. For that stronger equivalence one must additionally retain joint indicators 1_{duration=t, exit=(j,y)} (and terminal analogues); separate marginal tests are insufficient when duration and next entry correlate.

Embed this ACTUAL cylinder in the free Isbell envelope by the fully faithful base embedding and form its canonical comparison

    H_i <-[b_i in M_0] G_i ->[h_i in E_0] R_i.

Here H_i denotes the embedded operational path carrier, not a claim that the canonical carrier is a countable state space. By the established Fact(r) equations,

    b_i p_G = P,       h_i p_G=e,
    q_H b_i=q_G,      q_R h_i=q_G.

For every named entry x and test l, both routes therefore give the SAME scalar cylinder entry r(l,x). Full faithfulness identifies it with the original extended nonnegative number. Consequently each certificate inequality, with its fixed external v_i(x), is invariant under the actual compatible comparison span. This is not transport of a rank function along a formal arrow; it is transport of the evaluated entry/return/tail certificate through the actual two-sided cylinder.

An operational representative Y of this enriched cylinder means a supplied module implementation whose normalized UNCONDITIONAL preparation and genuine duration/return tests (including nontermination as above) factor this same cylinder. Conditioning its law on eventual return is not an operational realization of these tests. It inherits (1),(2) and any retained (5). When Y also satisfies the conditional invocation interface of section1, it may replace the original module in the wiring theorem. The canonical R_i itself has the numerical certificate on named preparations/tests, but is not thereby an operational representative. No stochastic section or executable realization of R_i is constructed or assumed to follow from CFS.

Existing compatible-span associativity/context coherence carries these scalar equalities coherently through finite normalizations. For actual operational representative networks the independently derived uniform tail bound (4) shows that finite-horizon termination probabilities converge to1; this obtains admission without claiming that free reconstruction preserves arbitrary countable colimits. Generic formal compact wiring is not silently identified with execution through these unbounded reward rows. The operational wiring bridge is precisely the fixed typed kernel invocation interface and the proved inequalities above.

## 4A. Stronger optional reconstruction: an executable marked boundary kernel

The compressed gain/tail cylinder above only carries bounds. A stronger version yields an actual positive reconstruction at the BOUNDARY, without claiming that the canonical CFS apex is an executable state space.

Let O_i be the countable disjoint union of terminal outputs and typed next entries (j,y). Retain, for every positive integer d and o in O_i, the joint test

    E_(d,o)(h)=1_{duration(h)=d and outcome(h)=o},

and E_infinity(h)=1_{h=infinity}, as well as the unit row. The genuine operational cylinder entries define directly

    F_i(d,o|x)=E_(d,o) P_x,     F_i(infinity|x)=E_infinity P_x.

They are nonnegative and their countable sum is1, because these events partition the normalized operational outcome space. This positivity/normalization fact is inherited from the actual input cylinder, NOT manufactured by an arbitrary formal CFS arrow. Compatible two-sided comparison preserves each named entry, so extracting F_i after reconstruction or before reconstruction gives exactly the same kernel. The tail certificate implies F_i(infinity|x)=0. No section of either comparison leg is needed.

This marked boundary kernel has a concrete countable operational realization. On entry x sample (d,o) according to F_i. Remember the countable pair (remaining duration, o), count down deterministically, and emit o at exactly the d-th step. The sampling transition counts as the first step, so d=1 emits immediately and d>1 enters countdown d-1. If an infinity atom is allowed before progress certification, send it to a distinguished nonterminating state. Thus the FULL marked-cylinder reconstruction produces a stochastic implementation at its original typed boundary. It need not reconstruct the original hidden mechanism, preserve intermediate observations, or be small; observation and intervention during an invocation were not part of this boundary language.

For the EXACT wiring statement in this subsection, use the exact-kernel branch of section1: conditional on the complete past and current entry, each invocation has the specified marked kernel F_i. The weaker alternative of merely satisfying conditional inequalities proves bounds but NOT equality of marked path laws. Hidden persistent state must be included in the entry if needed for this exact condition.

Actual wiring is explicit. On the joint entry space X=disjoint union_i X_i, let Q_d be the return-to-entry kernel of duration d and A_d the terminal-output kernel of duration d. The total terminal kernel of duration n is the nonnegative path sum

    W_n = sum_(k>=0) sum_(d_0+...+d_k=n, all d_l>=1)
                         A_(d_k) Q_(d_(k-1)) ... Q_(d_0),

using the column convention (rightmost kernel executes first). For each fixed n, only k<n contributes, though sums over intermediate entries may be countable. The total finite-exit kernel is sum_n W_n; any missing mass is nontermination. The progress theorem of section2 or2A derives that this missing mass is zero. It does not assume it while defining the wiring.

Convolution of durations is associative by associativity of addition, and regrouping intermediate states or invocation blocks is valid by Tonelli. Consequently extracting marked kernels then wiring equals forming the actual operational wired cylinder then extracting its marked kernel. Repeated finite gluing and alternative parenthesizations agree literally on all named duration/output probabilities. The resulting first-exit series also agrees under such regroupings, with no conditional-convergence issue; the quantitative tail proof separately establishes its normalization. This is an operational comparison/wiring law, not an assertion that Isbell reconstruction preserves an arbitrary countable limit.

Named endpoint changes also have an explicit law: precompose external entry labels by a deterministic map a:X'->X and push external terminal output labels forward by b:O->O', keeping duration (here O and O' denote the external terminal interfaces). The extracted entries become

    F'(d,o'|x')=sum_(o:b(o)=o') F(d,o|a(x')).

This agrees with the actual prep/test reindexing and is coherent under composition by Tonelli. Internal wiring changes require the same typed boundary maps to commute with the chosen wiring; arbitrary identification of internal states is not asserted to preserve dynamics.

Hence the stronger optional statement goes beyond scalar-bound invariance: complete countable joint boundary observations determine a positive semi-Markov interface, give an explicit countable countdown implementation, and commute with the specified serial wiring. They do NOT provide finite-data reconstruction, a small realization, a functorial implementation of arbitrary qualitative quotients, an implementation of the canonical Isbell apex, or compatibility with unobserved mid-invocation interventions. The compressed certificate version remains useful when complete boundary behavior is unavailable.

## 4B. A traced operational category of marked kernels

The preceding positive bridge can be placed directly in the structural theorem's source category. Let M have countable sets (on a fixed small skeleton) as objects. An arrow K:X->Y is a family

    K(d,y|x)>=0,  d in N={0,1,...},  with sum_(d,y) K(d,y|x)<=1.

Missing mass represents nontermination/nonreturn. Define

    (L K)(n,z|x)=sum_(d+e=n) sum_y L(e,z|y)K(d,y|x).

Identities put mass1 at (duration0, unchanged state). Associativity and unit laws follow from addition on N and Tonelli; column sums of composites remain at most1. Disjoint union is a symmetric monoidal tensor, with arrows operating blockwise and structural permutations taking duration0. This is a marked substochastic execution category; no native CFS on M is assumed.

For f:A+U->B+U, let its marked blocks be R:A->B, S:A->U, T:U->B, Q:U->U. Define feedback by convolution-composition

    Tr_U(f)=R + sum_(k>=0) T Q^k S.                           (8)

The coefficient at duration n is the sum of weights of finite first-exit paths whose nonnegative duration labels total n. Such finite path events are disjoint; their total mass for each input is at most1. Hence (8) is an arrow of M, even when Q has closed classes and even when there are zero-duration transitions. The sum over k may have infinitely many contributions to a single duration coefficient, but is monotone and bounded by1, so its existence does not require an inverse or convergence cancellation.

The Joyal–Street–Verity trace identities follow from the same first-exit path partitions as for ordinary countable substochastic kernels, with total duration carried as an additional additive label. Naturality attaches prefix/suffix paths; dinaturality moves the cut in alternating paths; vanishing partitions paths into maximal excursions through the two hidden interfaces; superposing retains disjoint branches; yanking is the unique matching duration0 path. Each partition preserves both the product of transition weights and sum of duration labels. Tonelli validates all countable regroupings. Thus M is a totally traced symmetric monoidal category for disjoint union. Totality here means that the trace is always SUBstochastic, not that every traced stochastic arrow remains stochastic.

Zero-duration transitions are necessary for identities and harmless for the algebra. An infinite run of zero-duration internal transitions does NOT become an exit at time0; it contributes missing mass. Operational invocations in sections1–3 have duration at least1, so infinitely many invocations imply infinite elapsed-step cost and no Zeno completion claim is made. More general zero-duration invocation interfaces would require a separate non-Zeno interpretation when discussing physical time, although the invocation-count/probability trace itself remains well defined.

Complete marked-cylinder extraction in section4A gives precisely an arrow of M after dropping the infinity outcome into missing mass. Its unit-mass observation plus infinity test identify that deficit exactly. Local tail certificates prove normalized local arrows, and the derived wiring progress theorem proves that the appropriate feedback (8) is normalized globally. No assumption that normalized arrows are closed under arbitrary feedback is introduced.

For clarity, forgetting time is a genuine functor U:M->CountSubStoch,

    U(K)(y|x)=sum_d K(d,y|x).

Tonelli proves preservation of composition, disjoint union, and (8). This functor loses quantitative timing information but not finite-exit mass. This is an optional concrete cross-doctrine map; it is not an inverse reconstruction or a canonical choice of timed behavior.

There are TWO ambient-cylinder constructions here, and they must not be conflated. Section4 uses Mat_[0,infinity] to type unbounded potential and cost rows. Those rows are NOT arrows of M. For the complete marked M-cylinder instead use actual boundary kernel F:X->O, deterministic entry selectors delta_x:1->X of duration0, and output indicator tests chi_o:O->1 of duration0. Its entry chi_o F delta_x is a singleton-to-singleton marked substochastic kernel, whose duration-d coefficient is F(d,o|x). Here 1 denotes a singleton, not the disjoint-union monoidal unit (which is the empty set); this 1-by-1 kernel is not a monoidal scalar. Thus this M-cylinder determines all finite marked-return probabilities; its deficit is determined externally by 1-sum_(d,o)F(d,o|x). Potential moments and tail bounds are evaluated externally from these complete preserved coefficients, not represented as substochastic morphisms with values greater than1. Equality of those coefficients preserves their nonnegative sums, including unbounded moments. This supplies the correctly typed operational cylinder for the following formal construction; no identification of its canonical middle with the different Mat_[0,infinity] middle is asserted.

Because M is an actual small traced source category, form its compact execution envelope Int(M), then its free Isbell envelope I(Int(M)). The already-established fixed-port cylinder construction, actual wiring carrier, and compatible M-left/E-right normalization spans apply to cylinders in this source. If the time-forgetting comparison is desired, the genuinely traced U induces Int(U), and the previously proved free reconstruction comparison applies to I(Int(U)).

The logical order is important: the marked operational trace and its laws are proved FIRST by path semantics; the complete boundary observations determine its original M-arrow; Int and free CFS then organize the actual comparisons and finite wiring coherently. We do not infer countable execution from compact trace over a Cartesian matrix tensor, nor infer that free Isbell normalization preserves arbitrary countable limits. The progress theorem supplies normalization/admission only for the certified original marked operational systems. Formal completion objects and canonical middles still acquire no automatic stochastic implementation.

## 5. Why the hypotheses carry content

The original upward-biased walk p=1/3 from1 has positive nontermination probability1/2. It cannot satisfy (2) with any finite v(1) and b(t)->0: its survival probabilities stay at least1/2. The downward and symmetric walk proofs above supply precisely the missing quantitative progress evidence; identical support does not supply it.

### Dropping quantitative gain information

Take a_i=2 and r_i=1 in each of two alternating modes, p_i=2/3. Each invocation finishes almost surely with finite expected duration; the assembled mission never finishes. Local termination does not imply global termination. Its gain matrix has spectral radius2 and cannot satisfy the strict weight inequality.

With a_i=2, r_i=1/2 in both modes, the mission does finish almost surely (the number of invocations is geometric), but its expected total duration is infinite: each surviving call doubles n while survival probability halves. Spectral radius1 is not a proof of nontermination, nor of impossibility; it marks failure of this contracting-potential certificate. Section2A directly repairs this: its invocation matrix has off-diagonal entries1/2 and spectral radius1/2<1, while G has spectral radius1. Thus (7) proves almost-sure completion with the original unbounded duration potential n. Do not report refusal of the stronger finite-mean certificate as impossibility.

### Dropping conditional validity / changing coupling

A module immediately returns on a Bernoulli event of probability r<1 and otherwise finishes. Fresh independent draws on each call give geometric termination and local potential v=1, gain r. Instead sample one hidden Bernoulli variable once and reuse it forever. Every isolated invocation started with that prior has the same marginal return probability r, duration1, and thus identical isolated scalar tests. But when wired to itself it fails to finish with probability r. After the first return the conditional return probability is1, not r. The second system does not implement the claimed reset kernel under invocation; isolated enriched rows alone cannot detect the missing coupling contract.

Thus this theorem requires an explicit reset/stateful operational interface. It does not solve the original broad local-to-global compatibility problem merely by renaming isolated observations, nor does it certify that an empirical black box has the required hidden-state discipline.

### Dropping tail information while preserving exit probabilities

A black box may have arbitrarily slow almost-sure stopping, so exit/gain rows alone provide no numerical physical-time tail. A return summary also cannot distinguish genuine local nontermination unless terminal mass and the invocation-completion semantics are retained. The countable family above supplies the local tail proof rather than assuming it.

## Exact scope

Proved: a countable operational module class, local quantitative tail/return interfaces, a finite wiring check deriving almost-sure global termination (with optional expected cost), and exact representative-independent invariance of those certificate entries under the genuine two-sided comparison of the enriched cylinder.

Also proved with the OPTIONAL complete marked boundary cylinder: extraction of a positive countable semi-Markov interface, a countdown operational realization, and exact serial wiring/endpoint-reindexing laws.

Not proved: executable canonical realization; generic stochastic maps underlying CFS legs; composability of isolated tests without reset/state accounting; all infinite-state termination; arbitrary feedback-preservation by free reconstruction; certificate discovery from finite evidence; novel ranking or small-gain theory.
