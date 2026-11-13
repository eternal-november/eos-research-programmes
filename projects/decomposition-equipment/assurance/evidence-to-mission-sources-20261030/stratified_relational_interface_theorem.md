# Exact stratified relational interfaces for finite linear port missions

2026-10-30. **Constructive theorem in a specified operational doctrine:** a finite rank/pivot stratification constructs exact operational RELATIONAL interfaces, witness sections, and coherent families of two-sided free-CFS comparisons for a declared finite linear port/context closure. Rank drops and original admission are retained. The method uses classical parametric Gaussian elimination and v2; no novelty or efficiency claim.

## 1. Precise doctrine and evidence

Let Theta be a nonempty semialgebraic parameter locus over real algebraic coefficients. Its parameters include UNKNOWN primitive matrices and coupling coefficients, with shared parameters literally shared across nodes. The locus is given symbolically by evidence and a declared structural theory, not by a full joint outcome table.

Fix finite typed ports, a finite port network syntax, and a finite declared closure L of the subnetworks, requested cuts, mission contexts, and wiring/substitution routes to be compared. The preparation/test indexing diagrams and their context maps are part of this finite declaration; no completeness for every context in a larger compact category is asserted. Every expression N has finitely many real wire variables w in R^(n_N), homogeneous linear constraints

    A_N(theta) w = 0,                                   (1)

and a fixed or polynomial external readout L_N(theta)w. Entries of A_N and L_N are polynomial in theta. The matrix A_N is assembled from the local constraints and matching/coupling equations by stacking their rows with the SAME theta. Internal wire variables are existential witnesses, not independently resampled parameters. Affine-in-wire constraints can be homogenized only with a distinguished coordinate fixed to 1; this note states and proves the homogeneous version used by the rank tests below.

The actual operational interpretation is the external linear relation

    R_N(theta) = L_N(theta)(ker A_N(theta)).              (2)

This is a declared linear-constraint doctrine. Unknown coefficients and joint constraints are allowed, but omitted physical topology/coupling laws are not discovered by elimination. Soundness for physics requires every actual case to satisfy this presentation and have this operational relation; completeness is relative to the declared model class unless its adequacy is independently justified.

For feedback retain a separate original admission predicate Adm_N(theta,context), when the original specification requires one. It may be semialgebraic, e.g. det(I-D)!=0 for inverse-Schur trace; a kernel-image or other original doctrine uses its own predicate. The existence of algebraic fixed points does NOT replace that predicate. If admission is not expressible in the selected theory, the interface construction still works algebraically, but the claimed decision/completeness result for operational admission does not.

A single policy/program and mission are fixed before theta: policy selection precedes universal quantification over supported worlds. An observable-adaptive program may use only its public observations. Internal Gaussian-elimination sections below are proof witnesses, not permission to use hidden parameters or a hidden rank chart when choosing actions. Every chart may be checked without experimentally determining which hidden chart is actual.

## 2. Finite common stratification and explicit interfaces

**Constructive lemma.** There is a finite semialgebraic cover of Theta by rank/pivot charts on which, simultaneously for every N in L, one can compute rational matrices N_N,H_N,T_N,S_N,D_N satisfying

    ker A_N = image N_N,                N_N has independent columns;
    L_N N_N = H_N T_N,                  H_N has independent columns;
    T_N S_N = I;
    ker T_N = image D_N,                D_N has independent columns. (3)

All denominators are explicitly nonzero on the chart. Zero-dimensional cases use empty matrices and satisfy the same formulas. Every specialization theta in the chart satisfies (3), including all rank-drop points in their own charts.

Construction: branch Gaussian elimination on whether each candidate pivot numerator is zero or nonzero. On a nonzero branch divide by that numerator; on a zero branch retain it as an equation and try another pivot. Each finite matrix produces finitely many branches. Equivalently, choose an r-by-r nonzero minor and require all higher minors zero. Row/column permutation and elimination reduce A to diag(I_r,0), yielding the free-variable kernel basis N. Form B=L N, then choose independent columns H spanning its image; solve B=H T using independent pivot rows of H. The selected columns give an identity submatrix in T, hence an explicit right inverse S. Eliminate T to obtain D. Refine the finitely many covers for the finite closure L to one common cover. Empty branches can be discarded by QE but need not be recognized to verify the formulas.

This is comprehensive Gaussian elimination, not an assumption that rank is generically constant. Parametric solutions including degenerate regimes are classical: see [Sit (1992)](https://doi.org/10.1016/S0747-7171(08)80104-6) and the explicit zero/nonzero-pivot branching in [Ballarin–Kauers, Sections 3–4](https://wwwbroy.in.tum.de/publ/papers/rwca02.pdf). One can use a disjoint 'first valid pivot' partition or retain overlapping charts with transitions. No rank-drop stratum is dropped. Empty-branch removal over the REAL semialgebraic locus uses real quantifier elimination; complex-algebraic consistency is not substituted for it.

The interface is the finite presentation

    external e = H_N c.                                  (4)

The full solution space is parametrized by

    w = N_N(S_N c + D_N z).                              (5)

Here c is uniquely determined by e; z accounts exactly for invisible internal freedom. To verify (5), write any w=N_N v. Since c=T_N v, v-S_Nc lies in ker T_N and equals D_Nz. Conversely every expression (5) solves (1) and has external readout H_Nc. Independence of N_N and D_N makes z unique after the chart bases are chosen.

Thus the construction extracts both an EXACT relation interface and a concrete lift of each external behavior, together with all hidden alternatives. It does not merely answer whether the mission holds. An equivalent implicit interface matrix annihilating image H_N can be computed by left-nullspace elimination.

## 3. Exact wiring and controlled section changes

Suppose two subnetworks have disjoint private wire witnesses and shared cut variables. Keep each cut variable in their external interfaces until they are glued. Then

    exists(private_1,private_2,cut) [constraints_1 and constraints_2]

is exactly the relational composite of their extracted interfaces, with the same theta. This follows by ordinary existential elimination: witnesses for the private variables can be combined because they are disjoint, while the cut variables and parameter tuple are shared. If a supposedly private variable actually couples both nodes, it must be retained at the cut or represented by a joint constraint; eliminating it independently is not valid.

Consequently direct extraction for the flattened A_N and extraction after relational interface composition describe the SAME subspace R_N(theta). Comparing their independent-column bases gives an invertible coordinate map, determined by the external legs. Associativity and substitution coherence follow because all routes have the same external relation and the unique coordinate map sending each basis vector to its represented external vector. This is exact relational-interface coherence, not a claimed uniqueness of internal solution sections.

Sections generally differ. Basis-free, let K=ker A, R=L(K), and q:K->R. A chart section s_i:R->K satisfies q s_i=id. On overlap,

    tau_ij = s_j-s_i : R -> ker q,
    tau_ik = tau_ij + tau_jk.                            (6)

These are invisible-kernel SHEARS. External basis transitions satisfy H_i=H_j F_ji and F_ki=F_kj F_ji; internal basis transitions and (6) give the corresponding block-triangular coordinate changes. Nothing requires one global section or a constant raw carrier rank. Rank changes are handled by distinct strata; overlap maps are used only where both charts represent the same spaces.

This addresses the distinction between external compatibility and nonunique internal witnesses explicitly. A section is a mathematical lift of an already admitted relation, not necessarily an executable control policy.

## 4. Actual two-sided CFS comparisons: the required typing

The subspace R_N is not automatically the canonical CFS middle of a deterministic linear MAP from input to output: the behavior can be nondeterministic. Use the category LinRel of finite-dimensional real vector spaces and linear relations, with direct sum as its compact monoidal structure. Composition is existential matching, and its compact trace is algebraic feedback/constraint closure.

If external space is X direct-sum Y and Hc=(H_Xc,H_Yc), the coordinate carrier C=R^(rank H) honestly realizes the relation by two labelled legs:

    preparation relation X -> C:  H_X c = x,
    test relation C -> Y:         y = H_Y c.

Their relational composite is exactly R_N. Prepending/appending the declared preparation/test contexts yields the whole admitted labelled cylinder. One raw carrier can serve all such contexts for the fixed core relation. Alternatively the full witness carrier K gives another honest realization. The quotient q:K->C sending a solution to its external coordinate c is an honest-realization morphism: surjectivity supplies every preparation into C, and its two external projections agree with those of K. A chosen witness section C->K generally is NOT an honest-realization morphism: it retains only selected preparations into K rather than the entire preparation relation. Formula (5) records these extra witnesses without falsely identifying the carriers or promoting arbitrary sections to realization morphisms.

Choose the FULL SMALL SKELETON of finite-dimensional real linear relations: objects are R^n for n>=0, and each hom-set consists of the linear subspaces of R^(m+n). The object collection and hom-collections are sets in the chosen universe, and all real theta-specializations are included. Direct sum, the diagonal cups/caps, and all required maps belong to this compact-monoidal category. Apply its free Isbell envelope K=I(LinRel_R). The established variance-aware comparison theorem (v2) constructs its canonical middle R_free and the actual compatible span

    raw honest carrier <-[M] comparison apex ->[E] R_free. (7)

Keep R_free distinct from the concrete relation space and the kernel basis carrier. Both concrete carriers are honest realizations, not asserted free-CFS canonical objects.

Chart transition isomorphisms preserve both external labelled legs. V2 naturality therefore transports (7) across charts. The actual wiring equality in Section 3 supplies the same-cylinder premise; v2 mixed-pullback preservation and rigidity then give the genuine comparison-span compositors, natural over Prep x Test^op. Their coherence is inherited from v2, while the observable coordinate transitions and section shear equations explain how the finite presentations fit together. Precisely, the raw assembly F_N of the selected local carriers has its v2 substitution compositor to the common free middle. A separately extracted composite relation carrier C_N has its OWN comparison to that middle. These spans have different raw left endpoints and are not identified without an explicit boundary comparison. Direct versus staged extracted relation bases are isomorphic by Section 3, so their own comparison spans are related by v2 naturality. This distinction prevents normalized endpoint agreement from being misreported as a raw-span isomorphism.

All comparisons are FAMILIES indexed by theta and the admitted contexts. No isomorphism of raw carriers across distinct ranks/worlds is required. Finite rational formulas explicitly present the RAW relational interfaces, witness sections, and chart transitions. The free-Isbell apices and legs in (7) are supplied by the established universal construction; this is NOT a theorem that they have finite rational-matrix presentations, computable finite sizes, or a finite effective representation algorithm.

The LinRel trace is only a proof presentation for the constraint relation. For an original partial feedback doctrine, use it operationally ONLY where the original Adm_N predicate is certified. Different parenthesizations/schedules retain separate guards. Neither the compact category nor its free completion authorizes execution outside that domain.

## 5. Evidence refinement and rank-drop exactness

For stronger evidence Theta' subset Theta, intersect every existing chart with Theta'. Restrict the SAME rational basis, interface, section, and transition formulas. Because all their denominators remain nonzero on that intersection, every identity (3)-(7) continues to hold at every supported point. Direct and iterated evidence restrictions are identical on these formulas; they commute with external relation extraction, wiring, and the canonical comparison families.

This is not a generic-flatness shortcut. The original cover included ALL pivot/rank branches, so points of smaller rank retain their own basis data. A generic chart cannot be specialized through a vanishing pivot; the rank-drop chart must be used instead.

A finite refinement can also split the charts by the finitely many original-admission predicates, so their truth patterns are constant on each chart. Construct only the required fully admitted rectangles. An unknown or false guard is not filled with a formal completed observation.

## 6. Complete mission tests in this relational doctrine

For a fixed network, let p:R^n->R^m be the required input projection and let r=O-Jp encode the stated linear mission readout. Then, for each theta:

    every solution satisfies r w=0
      iff ker A subset ker r
      iff rank([A;r]) = rank A;                         (8)

    every input u in R^m has some solution w with pw=u
      iff p(ker A)=R^m
      iff rank([A;p]) = rank A + m.                     (9)

Proof: (8) is the row-space/kernel annihilator identity. For (9), rank([A;p])-rank A equals rank of p restricted to ker A. Equivalently compute pN and test full row rank. On successful strata a right inverse of pN constructs an input-to-solution section; (8) guarantees that ALL alternative solutions satisfy the mission, not merely the selected section.

These are necessary and sufficient for the stated total relational mission. They impose no hidden-state uniqueness. If a mission permits only an input subspace, replace (9) by inclusion of that subspace in p(ker A); if the original mission has different quantifiers, its corresponding condition must be stated separately.

Conjoin (8), (9), and only the original admission guards required by the mission. QE checks whether the nonempty evidence locus lies inside the successful locus. Failure yields a parameter countermodel relative to the declared theory and, by elimination, either a violating solution or an input with no solution (or a failed original-domain guard). With real algebraic coefficients, nonempty semialgebraic counterexample sets have real algebraic witnesses. This does not imply that a countermodel is physically realized if T was merely a sound overapproximation.

One policy was fixed throughout. The solution section can depend on theta because it certifies existential feasibility, not a separately selected hidden-world policy. If the user requires an executable observable selector for internal nondeterminism, that is a further uniform-control obligation not proved by (9).

## 7. Optional algebraic explanation of why unstratified kernels fail

Let A:P->Q be a map of finite free modules over a commutative parameter ring R, K=ker A, C=coker A, and let R->S be a refinement. Put B=image A. The two exact sequences 0->K->P->B->0 and 0->B->Q->C->0 yield

    0 -> Tor_2^R(S,C) -> S tensor K -> ker(A_S)
      -> Tor_1^R(S,C) -> 0.                             (10)

Thus new specialized solutions can appear. Global flatness is not required for the mission: for a readout O:P->Z, the output-visible defect is the image of the well-defined map

    Tor_1^R(S,C) -> Z_S / image(S tensor K -> Z_S),

defined by lifting a Tor class to ker(A_S) and taking its output modulo old-kernel outputs. Different lifts differ by the image of S tensor K, so the map is well-defined. New solutions can be mission-invisible.

On a pivot chart with rank fixed by zero/nonzero-minor equations, elimination makes A equivalent to diag(I_r,0) over the corresponding quotient/localization. Its kernel is explicitly split free and commutes with further base change retaining the chart's inversions. This explains the pointwise exactness above without demanding global flatness. The theorem itself needs only the elementary chart calculation, not derived algebra. For A=[t] over R=R[t], the generic kernel is zero but at t=0 it is one-dimensional. The two charts t!=0 and t=0 retain both cases. With readout O=0 the new kernel is mission-invisible; with O=id it is visible. Thus neither generic-rank computation nor a blanket global-flatness requirement is the right mission test.

## 8. Exact result and limits

The construction EXTRACTS finite rational presentations, over a finite stratified cover, of relational interfaces, lift sections, invisible freedoms, and transition data for a finite declared closure. The established free-Isbell construction then supplies genuine v2 comparison families; finite effective presentations of those free apices are not asserted. It is complete for the stated linear relational mission plus specified decidable original guards, relative to its structural theory. Global symbolic inference is allowed; no local-computation or compactness advantage is asserted.

It does not infer hidden topology from evidence, validate a physically incomplete structural theory, replace an original partial trace with total relational trace, solve arbitrary non-linear-in-wire dynamics, ensure a uniform executable selector, or give unlimited-context completeness. Additional contexts can require additional strata/refinement computations. There is no claimed universal finite atlas for every unbounded context. Exact coefficients and exact evidence constraints are assumed; numerical stability, statistical uncertainty calibration, and safely acquiring experiments are not covered.

The ingredients are comprehensive parametric Gaussian elimination, relational composition, rank tests, and the already-proved v2 CFS span theorem. The value here is their exact linkage—especially all rank drops, original admission, section shears, and actual two-sided comparison families—not an established new theorem of algebraic geometry or a novelty claim. The extraction and relational-semantics baselines below establish the appropriate scope of that attribution.


## 9. Primary sources and attribution

- **William Y. Sit, _An algorithm for solving parametric linear systems_ (1992).** The established extraction baseline includes degenerate parameter values and uniform solutions on parameter regimes. [Primary publication](https://doi.org/10.1016/S0747-7171(08)80104-6).
- **Clemens Ballarin and Manuel Kauers, _Solving Parametric Linear Systems: an Experiment with Constraint Algebraic Programming_.** Sections 3–4 give constraint-maintaining zero/nonzero pivot branching and uniform-solution regimes. [Author-hosted manuscript](https://wwwbroy.in.tum.de/publ/papers/rwca02.pdf).
- **Brendan Fong, Paolo Rapisarda, and Paweł Sobociński, _A categorical approach to open and interconnected dynamical systems_.** A sound and complete relational/corelational compositional framework; Appendix C.3 identifies corelations of vector spaces with linear relations. Its trajectory semantics differs from the finite static systems here. [Primary text](https://arxiv.org/html/1510.05076).
- **John Baez and Brendan Fong, _A Compositional Framework for Passive Linear Networks_.** Theorems 1.1 and 7.7 establish compositional black-boxing into Lagrangian relations for the specified passive circuit class. [Primary text](https://arxiv.org/html/1504.05625).
- **Richard Garner, _The Isbell monad_.** Free cylinder-factorization systems; used through the separately established variance-aware reconstruction/comparison theorem. [Primary text](https://arxiv.org/abs/1410.7108).

The present linkage uses these established ideas together with the prior v2 comparison proof. It does not establish priority for parametric elimination, relational black-boxing, or a new general span calculus.
