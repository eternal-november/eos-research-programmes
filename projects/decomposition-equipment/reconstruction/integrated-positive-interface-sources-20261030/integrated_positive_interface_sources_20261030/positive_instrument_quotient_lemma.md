# Positive instrument realization from a context-generated predictive cone

2026-10-30. Constructive finite lemma and counterexample. This is a classical positive-cone/observable-subspace realization argument connected to the project's two-sided comparisons, not an asserted novelty result. It does not discover unknown transition laws from data.

## 1. Declared finite operational model

Let S be a known finite carrier, A a finite command alphabet, and O a finite observable-output alphabet. Column distributions are used. For each a,o let K_{a,o}:R^S->R^S be nonnegative, and suppose

    1^T sum_o K_{a,o}=1^T                 for every a.       (1)

Thus {K_{a,o}}_o is an action-output instrument, with output probability 1^T K_{a,o}p and unnormalized next state K_{a,o}p. The carrier includes all persistent shared sources, pending delays, and model indices needed for this finite description. Delay coordinates may be deterministic.

Unknown initial law p belongs to a nonempty evidence polytope

    E={p>=0: 1^T p=1, Bp=e, Fp<=f}.                      (2)

Known structural support constraints can be included. Only the initial law is learned in this formulation. Unknown primitive dynamics may be encoded by a known FINITE catalogue of mechanisms carried as a persistent model coordinate, with block-diagonal instruments, but this enlarges rather than discovers the catalogue and does not establish its physical adequacy.

Fix finitely many mission readout row vectors g_1,...,g_m. Let W be the least row subspace containing 1^T and these rows, and closed under

    w -> w K_{a,o}.                                    (3)

It is computed by finite linear-span closure and stabilizes in at most |S| dimension increases. These action-output maps, rather than unconditional action maps sum_o K_{a,o}, are essential for adaptive observation-based programs.

Choose a basis matrix Q with rowspace W and first row 1^T. Define q(p)=Qp. Invariance uniquely induces linear maps L_{a,o} on R^d=im Q such that

    Q K_{a,o}=L_{a,o} Q.                               (4)

Let C=Q R_+^S, a finitely generated pointed cone: its first-coordinate functional tau has tau(Qp)=1^T p, and tau(x)>0 for every nonzero x in C. Let P=Q Delta(S)={x in C:tau(x)=1}. This is a compact polytope. Each L_{a,o} preserves C and

    sum_o tau(L_{a,o}x)=tau(x).                         (5)

## 2. Construct a positive finite abstract instrument

Let v_1,...,v_r be the DISTINCT extreme vertices of P, and let V be their column matrix. There are at most |S| such vertices, since P is the convex hull of the columns Qe_s. For each a,o,i write

    L_{a,o}v_i=sum_j h^{a,o}_{ji} v_j,     h^{a,o}_{ji}>=0.   (6)

Such a decomposition exists because L_{a,o}v_i belongs to C. If its tau-mass is zero the vector is zero and use the zero coefficients. Otherwise normalize by its positive tau-mass, take a convex vertex decomposition in P, then multiply the coefficients by that mass. Define H_{a,o}=(h^{a,o}_{ji}). Then

    V H_{a,o}=L_{a,o} V,
    1^T sum_o H_{a,o}=1^T.                             (7)

The second equation follows by applying tau to each column of the first and using tau(v_j)=1 and (5). Therefore H is a positive normalized finite action-output instrument. No positive section P->Delta(S) or equivariant representative choice was assumed.

Choose a column-stochastic matrix C0:R^S->R^r such that

    V C0=Q.                                           (8)

This is constructed independently column by column, expressing each Qe_s as a convex combination of the vertices. For an initial law p use eta=C0p. Then Veta=Qp. More generally ANY eta>=0 with 1^Teta=1 and Veta=Qp gives the same permitted observations and mission tests.

The initial interface uncertainty can be represented by the positive polytope C0 E. Alternatively use the possibly larger polytope

    Ehat={eta in Delta(r): exists p in E, Veta=Qp}.      (9)

Every eta in (9) has a supported p and induces the same permitted-context laws as that p; enlarging from C0E to (9) does not introduce additional observable behavior. Keep this joint initial constraint. Rechoosing an independently supported initial law at each time step would add adversarial switching not present in the model.

## 3. Exact adaptive-context adequacy

For every finite word z=((a_1,o_1),...,(a_n,o_n)), write K_z and H_z in chronological composition order. Equations (4) and (7) imply

    QK_z p = L_z Qp = V H_z eta.                       (10)

For every g in W there is a unique row gbar with g=gbar Q, and consequently

    g K_z p = gbar V H_z eta.                          (11)

In particular 1^T K_z p=1^T H_z eta: the complete observable word probability is identical. Because actions selected by an observation-based policy are functions of the same observed prefix, every branch of a deterministic policy tree has identical probability. Summing branches proves equality for every finite adaptive policy and every mission event built from the declared outputs and readouts. Randomized policies are mixtures, or may use coupled private policy coins, so the equality persists.

The controller does not observe p, eta, or a hidden model index. The SAME policy is deployed in the true and abstract systems. Parameter-dependent initial-state lifts establish equality of laws; they do not select a different action policy for each world.

For a fixed finite horizon and a smaller declared policy language, one may instead use the backward spaces W_t generated by the remaining admissible suffixes and augment the state by t. This gives a layered positive construction without closing under unnecessary infinite-horizon contexts. The stationary W above is sufficient for all finite words, and may be stronger than the mission needs.

Positivity of reward/readout values is required only if their semantics calls for it. A general linear readout is transported algebraically by (11). Actual event probabilities use indicators/normalized test effects.

## 4. What partial evidence determines exactly

Evidence need not determine p or the whole primitive state distribution. It determines one unique predictive state Qp exactly iff Q is constant on E. This is decidable by finitely many linear programs: every row of Q has equal maximum and minimum over E. Equivalently W annihilates span(E-E).

This criterion is NECESSARY AND SUFFICIENT for equality of all tests in W on the initial evidence fiber. If W was generated by the mission/readout rows and actual admitted instrument words, equality of all those generator tests is equivalent to equality of their span. Thus the criterion derives adequacy for that specified generated context language, rather than assuming each context separately.

It is not necessary for a robust mission guarantee: different predictive states may all satisfy one threshold. In that case retain Ehat and certify the SAME policy uniformly over it. For any fixed finite policy, its failure probability is a linear functional of the initial distribution, so exact worst-case failure over Ehat is an LP. Optimizing over policies is a separate capability/planning problem, not solved by this lemma.

Approximate evidence usually gives a non-singleton predictive polytope. Exact data collapse is not promised from finitely many noisy samples. The lemma accepts whichever valid confidence/evidence region an acquisition theorem supplies, and makes no claim to derive that region safely or within a budget.

## 5. A compositional positive representative can be impossible although the quotient works

Let S={a1,a2,b}, and identify a1,a2 as A and b as B. Let command T fix a1,a2 and send b to a1; let command U fix a1,a2 and send b to a2. Observe only the quotient label A/B. Both commands induce the same valid two-state deterministic quotient: A stays A and B goes to A.

Suppose there were a stochastic section sigma of the quotient that commuted with both commands. Necessarily sigma(B)=delta_b and sigma(A)=lambda delta_a1+(1-lambda)delta_a2. Commutation at B for T forces sigma(A)=delta_a1; commutation for U forces sigma(A)=delta_a2. Contradiction.

Nonetheless the two-state quotient is positive, normalized, executable, and reproduces every permitted observation-based context exactly. It can be used operationally to select commands and assess mission guarantees. Requiring an equivariant positive representative in the ORIGINAL carrier would therefore repeat the overstrong lifting-contract mistake.

The cone construction permits a new realization, not a universally compatible section back into the old one. Different positive decompositions in (6) also need not give the same hidden transition matrix; they give the same labelled future cylinders by (10)-(11).

## 6. Two-sided cylinder and comparison typing

Take preparations indexed by p in the supported evidence set, or by a specified family of allowed preparation kernels; tests are the admitted suffix words and mission readouts. The original carrier R^S honestly realizes the scalar/vector cylinder through p and the rows gK_z. The abstract carrier R^r honestly realizes the SAME cylinder through C0p and the rows gbar V H_z. The predictive carrier R^d realizes it through Qp and the rows gbar L_z.

The maps Q:R^S->R^d and V:R^r->R^d are leg-preserving realization morphisms for these labelled cylinders. They need not be isomorphisms or admit positive sections. Under the previously checked v2 hypotheses, each honest realization therefore has its actual comparison to the common canonical CFS middle, and Q,V induce SOURCE-CHANGING double cells. Different choices of H and C0 give equal labelled cylinders; their raw carriers/transitions are not thereby identified.

The operational positive construction is proved above before invoking a completion. One may interpret its finite-dimensional maps in a compact linear ambient category to obtain the specified formal comparisons. This does not make all formal comparison apices positive/finite mechanisms, and it does not admit instantaneous operational feedback. Guarded temporal feedback is treated by its ordinary causal unfolding and persistent queue state.

Preparation covariance also needs care: C0 is linear in the original p, but there need not be an affine section choosing eta solely as a function of Qp. If preparation equivalences are quotiented further, use the family of lifts (9), or verify the demanded naturality separately. Do not infer a positive section from the existence of a positive realization.

## 7. Precise achievement and remaining step

This is a constructive positive context-adequate realization from a KNOWN finite instrument plus PARTIAL evidence on its initial law, allowing mission-specific observable closure and nonunique positive realization. It is stronger than simply selecting a feasible global representative, and weaker than full hidden-law identification or universal recovery.

It is not yet the desired discovery theorem. The finite carrier, primitive instruments, permitted contexts and completeness of their physical interpretation are supplied. A finite model catalogue can absorb parameter uncertainty, but listing that catalogue and checking its coverage is substantive. Unknown continuously parametrized dynamics or an unidentified latent topology are not learned by this lemma. A full acquisition theorem must establish the evidence region and the operationally relevant instrument representation from permitted observations without silently observing counterfactual response tables.

## 8. A small context-sensitive example without joint-law identification

A source block has hidden bits (X,Y) in {0,1}^2 with arbitrary unknown joint law p. Permitted commands may choose to read X OR Y and then terminate the block. Optionally they may first apply declared coordinate swaps/complements. Termination is part of the operational language, not a new probe that reveals a hidden mechanism or an assumed acquisition reset.

The nonterminal predictive rows are 1,X,Y. Their normalized predictive polytope is a square. Exact marginal data E[X]=u,E[Y]=v determine its predictive point while leaving correlation E[XY] unidentified. For u=v=1/2 the compatible joint laws include perfectly agreeing and perfectly disagreeing bits, plus every mixture. They all give the same permitted readout behavior. Positivity is retained by the vertex instrument construction; no joint table needs to be selected as physically true.

If the admitted context is enlarged so one actual source block can feed BOTH readouts, then the probability of observing (1,1) is E[XY]. The backwards action-output/test closure now contains XY. The old evidence no longer determines the predictive state. This is precisely a context-closure failure, not failure of positive realization in the original language.

No globally affine section from the square predictive polytope to probability distributions on its four corner states can be a right inverse: each corner must map to its own point mass, but the affine identity v00+v11=v01+v10 would require delta00+delta11=delta01+delta10. The contradiction illustrates why a positive realization family with nonunique mixture lifts is weaker than, and can exist without, an affine representative section. It also explains why 'copying the prediction' cannot be interpreted as independently resampling a hidden source.

## 9. Universal finite-horizon specialization, and its architectural limit

For a fixed finite action/output alphabet and finite horizon H, a finite physical state-space assumption can be replaced by a universal behavioral construction. Let T be the finite set of deterministic causal response trees: at each admissible action/observation history up to H, a tree specifies the next output for each available command. An unknown causal stochastic process admits a distribution p over T. For example, sample in advance an output for each history/command according to the process's conditional output kernel; the product distribution of these sampled entries yields exactly the process's observable law along every policy path. This is an existence representation, not a claim that all counterfactual tree entries are experimentally observed.

The hidden carrier records a response tree and the current history. Command/output updates are deterministic shifts with output filtering, hence form a known finite instrument. Initial laws are supported on root histories. Every factual experimental-cylinder probability is linear in p. Consequently a finite set of exact/interval partial-cylinder constraints has a causal positive extension iff its finite tree-law polytope is nonempty. The construction above supplies an operational positive realization for the generated context language; mission-specific robust conditions can be checked uniformly over the extension polytope. A selected feasible tree law is NOT assumed to be the true one.

This is a finite-horizon behavioral/causal-polytope baseline. It can be enormous and is not an efficient or nontrivial learning theorem. It also does NOT infer locality, independent sources, limited communication, intervention transport between different protocols, or a decentralized architecture. A universal global response tree can use every history symbol made available in its protocol; if an implementation cannot do so, the tree class must be restricted accordingly. Local deterministic strategy families with a shared random seed, or independent-source network models, require their own justified structural constraints. Products of independently fitted component marginals do not follow from feasibility of the global polytope.

Thus this specialization removes a supplied finite hidden-mechanism bound for finite interaction, but does not eliminate the model/architecture coverage obligation or solve the contract's separate constrained-agent matching requirement. Safe evidence acquisition and a useful structured decomposition remain additional work.
