# Calibrated reset frames and coupled stochastic ports

Status: proved sufficient-class construction, not discharge of the selected positive typed factorization target. The Cartesian geometry is established mathematics; the conditional kernel factorization and message minimization are also standard ingredients. This note makes their exact combined input/output boundary explicit and locates the still-hard hidden-interface step.

## 1. Derive a positive operational state space from recorded calibration

Assume the controlled readout process has observable Hankel rank at most N. The raw log contains N positive-probability preparation histories p_x and a recorded finite probe instrument with N mutually exclusive, exhaustive outcomes y. At the population-law level the prepared predictive state s_x satisfies probe_y(s_x)=delta_xy. This is an operational calibration assumption, not an assignment of physical subsystem identities. The preparations and probe must actually be present in the records under the required causal/exogeneity assumptions; there is no new experiment oracle.

The N prepared states and N probe effects are dual bases. Indeed their pairing matrix is the identity, hence rank is at least N, and the universe rank bound makes it exactly N. For every reachable conditional predictive state v, its coordinates in this basis are the probe probabilities probe_y(v), hence are nonnegative and sum to one. For a command/readout symbol z, the matrix entry K_z(x,y)=probe_y(s_x M_z) is the nonnegative probability of z followed by probe outcome y after preparation x. Summing over y gives the probability of z; summing also over outputs of a fixed command gives one. Thus the learned controlled law has an N-state positive stochastic realization, without claiming its states are the unique physical microstates.

The probe's state disturbance is irrelevant to the coordinate argument: probe_y is an effect used to read the pre-probe predictive vector. The simulator's transition matrix is reconstructed from that effect pairing, not asserted to execute a physical probe after every transition. Runtime controllers gain no new probe access.

Finite samples do not establish exact delta calibration or exact rank by themselves. A statistical use needs the rank/calibration class as an explicit universe assumption, a joint confidence family, and the finite-basis perturbation theorem. This note proves the exact population statement only.

## 2. Intrinsic reset-frame criterion

Work in the positive operational coordinates derived above. A proposer selects a finite family P_1,...,P_m of learned command-word kernels (summing over their readout outputs), possibly found by searching a declared finite word pool. No cut partitions are supplied.

Require:

1. Each P_i is row stochastic and idempotent.
2. P_i P_j=P_j P_i for all i,j.
3. Every diagonal entry P_i(x,x) is positive.
4. Let Q=product_i P_i and F_i=product_(j!=i) P_j. If R(P)={(x,y):P(x,y)>0}, require R(P_i) intersect R(F_i) to be the diagonal relation.

All conditions are finite identities/support checks on learned operators. Condition 4 is genuinely a whole-family condition, not merely pairwise independence of reset supports.

### Frame theorem

Let C be the set of support classes of Q. For c in C, let A_i(c) be the set of support classes of F_i contained in c. Then

    x |-> (c(x), [x]_(F_1),...,[x]_(F_m))

is a bijection X -> disjoint_union_c product_i A_i(c).

Thus the shared boundary C and dependent component coordinates A_i(c) are outputs. Their cardinalities may vary with c. Components of cardinality one can be removed as trivial.

### Proof

Set mu=uniform_X Q. Since products of the positive diagonal entries contribute to Q(x,x), mu is strictly positive. Commutation and idempotence give Q P_i=Q, so mu is invariant under each P_i and under every subproduct.

A finite stochastic idempotent with a faithful invariant distribution has no transient states. Each recurrent irreducible block is rank one (its only nonzero eigenvalue is its simple Perron eigenvalue 1), and its rows equal its invariant distribution on that block. Hence its support is an equivalence relation, and the kernel is conditional averaging within its support classes. In particular each P_i and F_i is reversible with respect to mu.

The support of a product of nonnegative matrices is relational composition. Therefore the support equivalence relations R_i=R(P_i) commute, their product is R(Q), and R_i meets the product of all other relations only in equality.

For two commuting equivalence relations R,S with R intersect S=diagonal, every R-class and S-class in a common R S-class intersect in exactly one point: existence follows from R S=S R, and uniqueness from the trivial intersection. This gives a Cartesian rectangle.

Apply this to R_1 and product_(j>1) R_j in each Q-class. The remaining R_j descend to the second factor and do not depend on the first coordinate: commutation with R_1 transports every R_j-edge across the first coordinate. Their independence conditions descend as well, since each original R_j meets the product of all the others only in equality. Induction yields the asserted bijection. QED.

The faithful calibration measure mu factors as a product on the A_i(c) coordinates conditional on c. Explicitly, F_i fixes every indicator f=1[A_i=a]. In the recovered geometry P_i averages f conditional on (C,A_-i), while Q averages conditional on C. The identity P_i F_i=Q therefore gives mu(A_i=a|C,A_-i)=mu(A_i=a|C). Strict full support and these identities for every i imply mutual conditional product structure. This describes the RESET geometry only. It does not assert that the actual initial law or ordinary environment transition law has this product form.

### Exact established baseline

The relation-theoretic condition is the atomic Cartesian decomposition criterion, not a new mechanism. Chen and Ponomarenko, Tensor products of coherent configurations, arXiv:2105.10679, Section 3, use pairwise commuting equivalence relations with each meeting the product of the others in the diagonal. Their Cartesian-lattice results supply the same set-level structure. The stochastic-idempotent reduction is the finite conditional-expectation/Markov-chain structure theorem.

Source: https://arxiv.org/abs/2105.10679

## 3. Why pairwise reset checks fail

On X=F2^2, let P_1,P_2,P_3 average respectively over the translation directions (1,0),(0,1),(1,1). All are stochastic idempotents with positive diagonal; they commute; every pair of support relations intersects only in equality. Nevertheless X has four states, not the eight states required by three binary independent axes. For each i, the product of the other two supports is universal, so condition 4 fails. The higher-order check rejects the redundant third direction.

This is a standard linear-dependence obstruction, useful for ensuring the proposed discovery procedure does not certify pairwise-only assembly.

## 4. Correlated dynamics through the discovered boundary

The actual initial distribution nu on X may be arbitrary and is retained, not replaced by mu. Implementing that joint initial law requires a separately admissible positive preparation protocol with all communication and shared randomness costs charged; retaining nu as a measure is not an initialization certificate. In this section u is a genuinely PUBLIC command available to the shared interface and all local kernels. Private command access cannot be inferred from this notation: it requires the residual-input/visibility treatment in the channel-cone note. In the recovered coordinates write an actual command kernel as

    K_u(c', a_1',...,a_m' | c,a_1,...,a_m).

Define the shared-boundary transition law

    Q_u(c' | c,a) = sum_(a') K_u(c',a' | c,a).

For clarity first assume Q_u(c'|c,a)>0 on every declared source/action/target-boundary row. Define the normalized conditional next-coordinate law

    H_u(a' | c,a,c') = K_u(c',a'|c,a) / Q_u(c'|c,a).

The discovered frame admits the following staged spatial realization if and only if these two finite conditions hold:

A. For every i, the i-th marginal of H_u depends on the source a only through a_i (and the declared c,c',u). Call it L_i,u(a_i'|c,a_i,c').
B. H_u equals the product of those marginal laws over i.

When they hold,

    K_u(c',a'|c,a)
      = Q_u(c'|c,a) product_i L_i,u(a_i'|c,a_i,c').

The construction first samples the shared interface c' according to Q_u, then updates each local coordinate through L_i,u. This allows arbitrary dependence of the shared transition on ALL local source states, and creates correlations among local next states through the common c'. It is not Daduna's unconditional product transition law.

Necessity follows by marginalizing any realization of the declared staged form. Sufficiency follows by the displayed construction. The same reconstructed kernels are reused at every time, so induction proves exact equality of all controlled trajectories from the SAME joint initial law, provided its initialization is separately admissible. No per-step selection of a different fitted world is allowed.

The criterion is explicitly relative to this staged interface type. If conditional next-state dependence remains after c' is fixed, this realization fails; it does not prove that every possible hidden/shared-innovation realization fails.

For zero Q rows, H is undefined. One must use support-indexed constraints with common local tables on every positive row. Arbitrary independent filling of the undefined rows can create a false realization. The strict-positive version avoids that additional partial-table completion problem.

## 5. Canonical minimal source messages

The shared interface does not automatically receive the whole source tuple. For each c and component i define

    a_i ~_i^c b_i

when Q_u(.|c,a_i,a_-i)=Q_u(.|c,b_i,a_-i) for EVERY u and every assignment a_-i of the other source coordinates. This is an equivalence relation. Let M_i(c)=A_i(c)/~_i^c and m_i be the quotient map.

Then Q factors uniquely through the tuple of messages:

    Q_u(c'|c,a)=Qbar_u(c'|c,m_1(a_1),...,m_m(a_m)).

Proof: changing coordinates one at a time within their equivalence classes preserves Q. Conversely, any deterministic local message maps through which Q factors can identify a_i,b_i only when a_i~_i^c b_i. Thus each message partition refines the displayed one. These are the coarsest component-local deterministic source messages for this shared-update law.

Similarly, with all relevant rows defined, quotient the command alphabet by equality of a local kernel table to obtain its coarsest local command view. Joint command availability remains the actual relation induced by original commands; it must not be replaced by an independent product of local command views.

This minimization is a canonical finite sufficient-statistic construction, not a novel lower-bound mechanism. Its role is to prevent a construction from silently granting every component the entire global state. A meaningful type universe must separately bound permitted message sizes/visibility and the description cost of Qbar. Failure of those bounds is a genuine failure of THIS typed realization, not permission to enlarge ports without accounting.

## 6. Crossing cuts and what is actually reconstructed

For every subset I of coordinate indices, the learned coarse cut retains c and (a_i)_(i in I). For crossing I,J, their overlap is c plus the coordinates in I intersect J, and their common refinement is constructed by the full recovered coordinate system. The corresponding calibration conditional expectations obey E_I E_J=E_(I intersect J), where E_I=product_(j notin I) P_j.

The actual joint initial and transition records must still be pushed forward as JOINT records; replacing them by a product of cut marginals would lose correlations. The staged kernel factorization above gives a particular positive joint witness across these cuts. Regrouping its actual factors preserves its whole controlled law by finite summation. This is not a theorem that arbitrary separately learned cuts have a common refinement.

## 7. Growing coupled family and cost boundary

For any m, take c and a_1,...,a_m binary. Calibration reset i independently replaces a_i by a fair bit while retaining c and the other a_j. These operators satisfy the frame criterion. Ordinary dynamics may instead obey

    c' = c XOR a_1 XOR ... XOR a_m XOR N_0,
    a_i' = a_i XOR c' XOR N_i,

with mutually independent noises N_0,N_1,...,N_m and 0<P(N_0=1)<1, P(N_0=1) != 1/2. The actual initial law can have arbitrary global correlation. The source message of every a_i is necessarily its bit, because changing it changes Q. The shared computation is a one-bit parity accumulator with a linear-size XOR circuit, not a message carrying the whole global state. Different local updates are correlated through c'.

This is a genuinely coupled growing family, not independent product padding. But a full calibrated N-state predictive realization here can have N=2^(m+1). The construction above is polynomial in the supplied/learned N-dimensional representation, NOT polynomial in m. It does not solve the selected target's desired scalable direct-local inference problem. Logged calibration also requires actual appropriate coverage; no free preparation oracle is assumed.

## 8. The remaining hard problem

The result gives an honest data-derived sufficient class: calibrated positive operational coordinates, unknown reset-frame cuts, and a reconstructed correlated shared boundary with minimal deterministic incoming messages. It is not the general positive typed factorization theorem and should not be marketed as such.

The hard extension is to discover a NEW shared stochastic interface when the observable reset boundary c' does not screen off the local updates. That requires simultaneous nonnegative factorization of many source/action-indexed kernels, with one persistent mechanism, permitted command visibility, and compatibility across alternative crossing frames. Choosing one arbitrary whole positive cone does not solve it; nor do independent local nonnegative factorizations. Generic semialgebraic existence encodings are a baseline, not the desired intrinsic operator criterion.

A further hard extension removes complete simplex calibration and works directly with signed observable representations and nonunique positive local cones. The current proof does not do that. These are precise unresolved structural floors rather than routine implementation omissions.
