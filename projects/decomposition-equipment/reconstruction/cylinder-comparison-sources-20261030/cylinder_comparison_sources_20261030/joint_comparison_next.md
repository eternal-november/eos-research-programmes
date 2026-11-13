# Joint-cylinder next comparison: mixed-corner spans and witness obstruction

Status: elementary derivations in the stated doctrines, not a novelty claim. The principal result is genuinely about arbitrary cylinder factorization systems (CFS); the relational network calculation separately makes a concrete gluing obstruction computable. Neither identifies a formal free object with a physical implementation.

## 1. Actual CFS theorem: reconstructing a rectangle of joint contexts

Let C carry a CFS (E,M). All indexing categories and cylinders lie within its chosen smallness doctrine. Fix an **actual** cylinder s:D⇒T with preparation category A and test category B. For any indexing functors i:P→A, j:Q→B, choose its canonical factorization

    Di --e_PQ--> R(P,Q) --m_PQ--> Tj.

These are joint profiles: P and Q need not be products, discrete, independent, or locally realizable. The input is the stated cylinder including its cross entries, not only marginal observation tables.

For simplicity write P⊂P′ and Q⊂Q′ for restrictions; the proof also works for arbitrary commuting indexing functors. There are canonical arrows

    R(P,Q) → R(P′,Q)                 (enlarge preparations),
    R(P,Q′) → R(P,Q)                 (restrict tests).

**Proof.** For the first arrow use orthogonality of the E-cocone e_PQ against the M-cone m_P′Q: the top cocone is e_P′Q restricted to P and the bottom cone is m_PQ. Their common cylinder is s|P,Q. For the second use e_PQ′ against m_PQ, with top cocone e_PQ and bottom cone m_PQ′ restricted to Q. Each diagonal is unique. END.

Every rectangle commutes. Its two routes preserve the same preparation legs and test legs, and orthogonality of its upper-left E-cocone against its lower-right M-cone forces equality. The same argument proves identities and composition. Thus R is a functor of preparation contexts covariantly and test contexts contravariantly (up to the canonical isomorphisms of chosen factorizations).

**Mixed-corner comparison.** An enlargement in BOTH contexts supplies the span

    R(P,Q)  ←  R(P,Q′)  →  R(P′,Q′).                    (1)

No E/M preservation by a wiring operation, generating/separating hypothesis, cofinality, or context adequacy is used. The middle is reconstructed from the actual mixed cylinder, not invented by guessing a map between two-sided quotients. The reverse mixed corner R(P′,Q) similarly supplies a cospan. In fact the left leg belongs to E₀ and the right leg to M₀, though they need not literally be epis/monos. For the left leg h, the relation h e_source=e_target between E-cocones proves h∈E₀: a lifting problem for h against an M₀-arrow first lifts using e_target; equality after h follows by uniqueness for e_source. Uniqueness follows using e_target again. Dually the common full M-cones prove the right leg lies in M₀. Neither leg is asserted invertible. These polarities differ from the earlier same-cylinder honest-realization span.

### Derived oplax coherence, without imposing exactness

For nested enlargements (P0,Q0)⊂(P1,Q1)⊂(P2,Q2), the direct span has apex R(P0,Q2). Grid functoriality gives a commuting cone

    R(P0,Q2) → R(P0,Q1),
    R(P0,Q2) → R(P1,Q2),

whose composites to R(P1,Q1) coincide. If C has the relevant pullback there is consequently a canonical arrow

    R(P0,Q2) → R(P0,Q1) ×_[R(P1,Q1)] R(P1,Q2).          (2)

It preserves the exterior legs to R(P0,Q0) and R(P2,Q2). Therefore (2) is a 2-cell from the direct comparison span to the composite of the two comparison spans. Depending on lax/oplax terminology this is an oplax compositor; the displayed direction is definitive.

For three or more enlargements, all composites of these 2-cells have the same projections into every mixed-corner factor, by grid functoriality. The universal property of iterated pullbacks makes them equal. The identity span and unit comparisons are identities up to the chosen pullback unit isomorphisms. This proves the full associativity/unit coherence for the declared context-enlargement category, not merely pairwise existence of spans. If C lacks pullbacks, the canonical commuting cones still exist; no bicategory Span(C) is then asserted.

Invertibility of (2) is an **additional conclusion to establish**, not a premise of the construction. For example, in Set it demands existence and uniqueness of a direct mixed witness for every compatible pair of intermediate reconstructed witnesses. A merely regular-epi comparison would guarantee existence but not uniqueness. No such claim follows from CFS axioms.

### Set specialization: a non-tautological exactness test

For the standard Set cylinder factorization, take a scalar table s:P′′×Q′′→K by assigning each preparation a singleton and each test the set K. Then R(P,Q) is the image of the row map P→K^Q. Dropping tests restricts row functions and is surjective; adding preparations includes row-image sets and is injective.

In (2), the comparison is always injective. Identify its codomain with the Q2-row profiles realized by P1 whose Q1 restriction is realized by P0: the first pullback coordinate is uniquely determined by that restriction. Its domain consists exactly of the Q2-row profiles realized by P0. Thus (2) is onto **iff every Q2-profile realized in P1 whose Q1-profile was already realized in P0 is itself realized in P0**. This is a checkable preparation-saturation condition relative to the actual future test refinement, not a blanket preservation axiom.

For strictness take P0={a}, P1={a,b}, Q1={t}, Q2={t,u}, and rows a=(0,0), b=(0,1). The direct apex has one element; the pullback composite apex has two. Every displayed comparison is well-defined, but the second preparation acquires a distinction only under the later test u. This exactly witnesses the noninvertible compositor.

### Why this advances, and where it stops

This compares genuinely different joint cylinders and has a derived noninvertible coherence law. It is stronger than the existing same-cylinder realization span. It requires only the explicit joint incidence that the question proposes as input. It does NOT reconstruct that incidence from local tables; does not identify R(P,Q) with a wired tuple of local R_i; and context-enlargement composition is NOT arbitrary physical cut. For a free local-product cylinder, the previous independent-product Isbell theorem can identify the starting corner if that corner really is the product-indexed cylinder. For correlated support use the actual restricted joint cylinder, not that product identification.

**Free-Isbell joint comparison, explicitly.** Let s be the actual joint cylinder in C, and suppose its restriction along preparation/test indexing functors is literally the independently wired cylinder W(r1,…,rn), including its entries. Apply the theorem to the Yoneda-image cylinder Ys in IC. The previously proved independent-product identity identifies the starting middle, yielding the constructed span

    W_I(R_free(r1),…,R_free(rn))
        ← R_free(s restricted to local preparations and ALL joint tests)
        → R_free(s).

The right endpoint is the reconstruction of the actual supplied JOINT cylinder, including correlated contexts; it is not replaced by a product. This gives the requested formal local-to-joint comparison without claiming the independently wired free object already realizes all joint observations. The left leg is E₀ and the right M₀ in IC. Noninjective indexing functors permit identification/repetition of declared contexts, provided the entries actually commute. If the local product cylinder is not an admitted restriction of the joint one, this particular span is unavailable; one must use the explicitly supplied incidence correspondence instead. The displayed formula alone says nothing about physical implementation or finite size.

To transport this construction to a family of actual wiring/gluing operations, one must exhibit their maps of the declared joint cylinders or their witness spans. This is specific semantic data, not an E/M preservation assumption. Section 2 gives the universally available witness-level comparison when the interaction is explicitly relational.

## 2. Concrete finite-network theorem: quotient gluing inserts kernels

Choose a typed collection of raw interface sets X_a and surjections q_a:X_a→Q_a. These can be either preparation or test record quotients, or jointly specified boundary records. For each admitted primitive interaction v give an arbitrary relation

    H_v ⊂ ∏_(ports p of v) X_type(p).

This is an explicit JOINT relation, not the product of its marginals. External interventions and correlated preparation/test seeds are additional relation nodes. Define its reduced relation by direct image

    bar H_v = (∏q)_! H_v.

A finite admitted wiring network N connects ports of equal type. Its raw solution set consists of one tuple in each H_v whose coordinates agree on every glued wire. Project to external coordinates and then apply q; call the resulting external relation A_N. Compose the reduced primitive relations by the same wiring; call that external relation B_N.

Put K_a={(x,x′):q_a(x)=q_a(x′)}. Define a *kernel-relaxed raw solution* by requiring K_a-related, rather than equal, coordinates at glued ports.

**Theorem.** B_N is exactly the quotient image of the kernel-relaxed raw solutions. Consequently

    A_N ⊆ B_N.                                        (3)

The inclusion is an equality iff every external quotient tuple of a kernel-relaxed solution has at least one genuine equal-wire solution with that same external quotient tuple. This is support exactness, not a claim that every relaxed witness lifts individually.

**Proof.** A tuple in B_N has a tuple in bar H_v at each node with matching quotient coordinates. Choose an H_v witness for each node (only finitely many choices). Matching quotient coordinates says precisely that the resulting raw port coordinates are K-related. Conversely any such raw tuples map to a compatible family of quotient tuples. This proves the formula for B_N. Equality implies K-relatedness on every wire, proving (3). The stated criterion is exactly surjectivity of genuine raw solutions onto the external quotient image of relaxed solutions. END.

This is a concrete formula for the failure: an explicit equality constraint was relaxed to the explicit kernel of discarded local information. It does not merely name an unspecified adequacy condition. A failed instance supplies a finite certificate: primitive witnesses, kernel-matched wires, external quotient tuple, and absence of a simultaneous genuine solution (decidable by finite search when all tables are finite).

### Single cut and coherence

Write composition right-to-left. For R⊂X×Y, S⊂Y×Z, let Q_R=q_Y R q_X^op and Q_S=q_Z S q_Y^op. Then

    Q_S Q_R = q_Z S K_Y R q_X^op,
    Q_(SR)  = q_Z S R q_X^op ⊆ Q_S Q_R.               (4)

Thus no choice of representatives is hidden. Every iterated composite inserts precisely one K at each cut. Rebracketing preserves the resulting formula by relational associativity; the inclusions are coherent since Rel is locally posetal. For arbitrary finite networks the same statement follows from conjunction and existential quantification, including the symmetry of wire rearrangement. This is an actual always-defined controlled comparison, albeit generally only a support overapproximation.

Outcome-sensitive observations are included by adding a terminal outcome port K with identity quotient. Then (3) compares sets of possible observed outcomes, not just anonymous existence of an internal record. It does not give probabilities or quantitative error bounds. A scalar-valued pairing factors through its proposed two-sided quotient only when each nonempty quotient fiber of the observation graph has a unique outcome; if it has several, retain that set or the witnesses rather than invent a scalar.

For nonfunctional local-to-joint comparisons, supply an incidence relation H between local preparation records and actual joint preparations (and separately for tests). Its image under the local and joint quotients is the canonical comparison relation. It is single-valued precisely when all joint witnesses over a fixed local quotient tuple have the same joint class. The kernel calculation applies to composing these relations. Existence of the incidence relation must come from the stated interaction; it is not generated by local observations alone.

## 3. Sharp feedback obstruction, even after perfect serial behavior

This paragraph concerns ONLY admitted algebraic relational feedback: closing two ports imposes equality of their values, equivalently the existential fixed-point trace in (Rel,×). It does not describe causal guarded evolving feedback with an initial state, nor stochastic normalization.

Let X={0,1}, q:X→1, and let σ swap 0 and 1. Give X only a constant local observation, so its local row quotient is q. The primitive swap preserves that observation. Its quotient is the identity relation on 1. Every word of swaps has nonempty raw relation, and its quotient is the identity; every serial cut of these declared words is therefore exact. In fact q is stable under both forward and reverse transitions.

Closing one swap has no raw solution x=σx, hence A_N is empty. Closing its reduced identity has a solution, hence B_N is the singleton closed observation. This proves that even exact serial composition for the declared generators and two-sided transition stability do not imply feedback exactness. The lost datum is the compatibility of witnesses *around the cycle*, not an unproved E/M property.

A minimal acyclic-cut counterexample is R:1⇝X selecting 0 and S:X⇝1 accepting only 1. Then SR is empty but Q_S Q_R is nonempty. Here the quotient witnesses at the shared class are different raw representatives.

### Explicit fiber transport criterion (bijective network special case)

Suppose each network edge is the graph of a bijection f_e:X_u→X_v and there are quotient bijections bar f_e with q_v f_e=bar f_e q_u. Fix a compatible quotient assignment (c_v). Each f_e restricts to a bijection between fibers F_u=q_u^-1(c_u) and F_v=q_v^-1(c_v).

For a connected finite graph choose a root and spanning tree. Transport along the tree identifies every fiber with the root fiber F. Each non-tree edge then induces a permutation h_e of F (tree transport to its source, f_e, and inverse tree transport from its target). There is a genuine raw lift of the quotient assignment iff

    ∩_(non-tree edges e) Fix(h_e) ≠ ∅.

**Proof.** A chosen root element uniquely determines all tree coordinates. The remaining edge equations hold exactly when that root element is fixed by every h_e. Conversely any joint fixed point gives all coordinates and satisfies every edge. END. For a single cycle this is the fixed-point test for its composite fiber transport; the swap example has a two-point fiber and fixed-point-free transport. This is ordinary elementary covering/descent reasoning, not a novelty assertion. General relations require simultaneous constraint solving, not just permutation fixed points.

## 4. Exact repair and honest limit

Keep each primitive's raw witness and its raw interface projections until all intended cuts are imposed; take the relevant pullbacks/equality constraints first, then take exterior quotient images. This constructs A_N and respects rebracketing of finite gluing. It is the exact witness/profunctor-style construction already implicit in ordinary relational semantics.

This repair does NOT show that a small sufficient summary exists, does not turn the raw space into a compact implementation, and may retain exactly the hard joint problem. Its role is to locate what a proposed smaller reconstruction must preserve: simultaneous liftability of quotient-matched witnesses. The fiber criterion above sometimes derives that property, or its precise failure, from primitive equations. Without such additional structure the kernel-relaxed object B_N is the defensible compositional overapproximation; calling it an exact reconstructed system would be false.

## 5. Literature and doctrine boundary

- Garner, *The Isbell monad*, https://arxiv.org/abs/1410.7108 : CFS/free-Isbell infrastructure. The mixed-corner result above is derived directly from CFS orthogonality; no claim that Garner states this particular span theorem.
- Shulman, *Framed bicategories and monoidal fibrations*, https://arxiv.org/abs/0706.1286 : known double-categorical setting for vertical maps, horizontal spans/proarrows and base change. Not a theorem of observational adequacy.
- Shulman, *The 2-Chu-Dialectica construction and the polycategory of multivariable adjunctions*, https://arxiv.org/abs/1806.06082 : known polarized/poly/double framework. The Rel kernel calculation is not itself a double-Chu preservation theorem.
- Joyal–Street–Verity, *Traced monoidal categories*, https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/abs/traced-monoidal-categories/2BE85628D269D9FABAB41B6364E117C8 : foundational trace framework. The explicitly defined cartesian relational fixed-point closure and swap counterexample above are independently checked calculations, not an attribution to a named result there.

Section 1 is genuinely general-CFS, but only for actual context-cylinder maps. Sections 2–4 are genuinely wiring/cut/finite-feedback comparisons, but in the explicitly relational doctrine. Combining them into a universal physical reconstruction theorem would require a verified bridge from that operational doctrine to the chosen CFS realization, including the actual joint cylinder. No such bridge follows from either construction alone.
