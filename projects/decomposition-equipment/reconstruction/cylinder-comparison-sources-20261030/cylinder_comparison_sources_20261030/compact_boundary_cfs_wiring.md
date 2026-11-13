# General CFS bridge: wiring decorated realizations through dualizable boundaries

Status: direct application of standard compact-boundary string-diagram calculus and CFS orthogonality; no novelty claim. This gives a structural sufficient doctrine for actual joint reconstruction/wiring compatibility. Unlike an E/M-preservation assumption, its extra structure is stated independently of reconstruction: a symmetric monoidal interpretation and dualizable matched wire objects.

## 1. Data and theorem: genuinely port-shaped cylinders

Let C be a symmetric monoidal category with a cylinder factorization system in a chosen smallness doctrine. Every admitted internal wire is labelled by a chosen dualizable object W. Fix its dual W*, coevaluation I→W⊗W*, and evaluation W*⊗W→I, satisfying the two snake equations. Only wire objects must be dualizable; local reconstruction middles and external preparation/test objects need not be.

A primitive vertex v carries a PORT-SHAPED cylinder

    r_v(p,t): A_v(p)⊗U_v → B_v(t)⊗V_v,

where U_v,V_v are fixed ordered tensors of operational input/output wire objects, while A_v(p),B_v(t) may vary with the preparation/test indices. Its supplied two-sided realization is

    A_v(p)⊗U_v --e_v(p)--> M_v --m_v(t)--> B_v(t)⊗V_v,
    m_v(t)e_v(p)=r_v(p,t).

These may be the canonical local CFS factorizations; arbitrary honest local realizations also work. Both labelled legs are retained. Primitive scalar experiments do not by themselves declare such wire interfaces or their connection law; those belong to the interpreted operational language. Singleton-index interface arrows I_v→O_v are included as a special case.

Let N be a finite directed wiring network connecting matched FIXED wire factors of the U_v,V_v. Cycles are admitted only with the compact algebraic feedback semantics declared below. Some wire factors may remain as an external input U_ext and output V_ext. The network may use an arbitrary joint preparation index P and joint test index Q, with given indexing functors p↦p_v and t↦t_v into the local index categories; they need not range independently. The external diagram objects are

    D_N(p)=(⊗_v A_v(p_v))⊗U_ext,
    T_N(t)=(⊗_v B_v(t_v))⊗V_ext,

up to stated symmetries. Reindexing retains the declared correlations. A genuinely extra joint preparation/observation fragment not described by this reindexing is supplied as an additional joint node, not inferred from its marginals. More generally, supplied outside preparation/test maps may be attached afterward.

Any through-wire with no primitive vertex can be represented by an identity vertex, so no equality constraint is silently omitted.

**Theorem.** From the local decorated realizations and the wiring alone, one constructs a SINGLE object Z_N independent of p,t and natural legs

    D_N(p) --p_N(p)--> Z_N --q_N(t)--> T_N(t)

whose composite is the actual interpreted joint network cylinder r_N(p,t). Canonical CFS reconstruction therefore has a naturally induced comparison

    Z_N ← U_N → R(r_N),

with left leg in M₀ and right leg in E₀. No claim that tensoring or feedback preserves E or M is needed.

The normalized reconstructed middles are coherent under all declared finite network equations valid in this compact-boundary semantics. Raw carriers have coherent flattening but need not be unchanged by inserting identities or by CFS normalization of subdiagrams. Fixed matched wire types are essential: arbitrary cylinders whose proposed wire objects vary with both p and t are not covered by the formula.

## 2. Explicit global factorization—the essential derivation

Let W be the tensor of all internal wire objects and M=⊗_v M_v. Tensor the primitive preparation legs, and separately the primitive observation legs, using symmetries to collect exterior and internal wires. For each p,t this yields

    e_p:D_N(p)⊗W→M,
    m_t:M→T_N(t)⊗W,
    F_pt=m_t e_p:D_N(p)⊗W→T_N(t)⊗W.

The interpreted network entry is exactly the compact trace over the matched internal wires:

    r_N(p,t)=Tr_W(F_pt).

Define

    Z_N=M⊗W*,
    p_N(p)=(e_p⊗id_W*) (id_D_N(p)⊗coev_W).

Define q_N(t) by applying m_t⊗id_W*, then permuting W⊗W* to W*⊗W in the output, and finally applying id_T_N(t)⊗ev_W. Associators are suppressed. Crucially W and M, hence Z_N, do not depend on p or t.

Then

    q_N(t)p_N(p)
      =(id_T_N(t)⊗ev_W)(symmetry)
        (m_t⊗id_W*)(e_p⊗id_W*)(id_D_N(p)⊗coev_W)
      =Tr_W(m_t e_p)
      =r_N(p,t).

This equality is derived from the declared compact wiring semantics and the local equalities m_v(t)e_v(p)=r_v(p,t). Naturality in p,t follows from the local cylinder legs and functoriality of tensor/composition. Graphically every internal boundary is opened by a cup on the preparation side, its dual is carried across the cut, and the corresponding source output is matched by a cap on the observation side. All joint internal assignments remain connected; no product of marginal contexts is substituted.

Additional exterior preparation maps d_a:D'_a→D_N(p_a) and tests o_b:T_N(q_b)→T'_b compose with these displayed legs, yielding the corresponding actual restricted/extended cylinder. This supplies the honest-joint-realization premise previously missing from the abstract span comparison. No global closed-experiment table has been independently assumed.

## 3. Derive the CFS comparison, rather than assume preservation

Factor the displayed external preparation cocone through Z_N:

    D --u--> U_N --j--> Z_N,      u∈E, j∈M₀.

Factor the observation cone restricted to U_N:

    U_N --a--> V_N --v--> T,      a∈E₀, v∈M.

The composite a u belongs to E: any lifting problem against an M-cone is solved first with u and then with a, and uniqueness is proved in the same two stages. Hence

    r_N=v(a u)

is a cylinder factorization. By uniqueness, V_N≅R(r_N), giving

    Z_N ←[j] U_N →[a] R(r_N).

Only in a doctrine where M₀ are actual monos and E₀ actual quotients should this be called a literal subquotient. The proof uses no preservation of either class by tensor, caps, cups, or other wiring.

For singleton-index exterior data this reconstructs the canonical arrow-factorization middle of the network arrow. For general port-shaped exterior families it reconstructs their actual observed cylinder, without assuming those families generate/separate any larger exterior interface.

## 4. Coherence with substitution, normalization, and interventions

### Raw flattening

If a network is first assembled from subnetworks using their unnormalized carriers, each subnetwork contributes its tensor of local M_v and the duals of its internal wires. The outer assembly contributes the remaining internal-wire duals. Tensor associativity, symmetry, and the coherent tensor-dual identification give the canonical isomorphism to

    (⊗_v M_v) ⊗ (⊗_e W_e)*.

Both preparation and observation maps become the same collection of cups, local legs, and caps. Symmetric monoidal/duality coherence makes flattening independent of parenthesization. This is a genuine witness-preserving finite-gluing law before normalization.

### Normalized wiring

Alternatively factor each interpreted port-shaped subnetwork cylinder canonically, and use its canonical middle with BOTH factorization legs as the local decoration in the outer construction. Its recomposed entries are still the same subnetwork entries, with the fixed exposed wire factors retained. Provided the declared joint reindexings match under the substitution, Section 2 therefore gives the same final network cylinder. Both final normalized middles are canonical factorizations of that one cylinder, so there is a unique isomorphism preserving all its preparation and test legs.

Every coherence diagram of these isomorphisms commutes: its routes preserve the same E-cocone and M-cone, and their orthogonality forces equality. This gives associative/unital normalized composition and compatibility with the declared compact feedback equations. It does NOT require the raw carriers of normalized versus unnormalized subnetworks to be isomorphic.

This is an actual wiring action on decorated realizations followed by canonical normalization; it is not an operation on bare middle objects stripped of their legs. Inserting an identity vertex, changing a parenthesization, or using a declared compact string-diagram equation leaves the interpreted cylinder entries unchanged, and therefore leaves its canonical reconstruction unchanged up to these coherent isomorphisms. A raw identity insertion may enlarge Z_N, so no stronger raw unital claim is made.

### Naturality, precisely

A map of local realizations k_v:M_v→M'_v is required to satisfy k_v e_v=e'_v and m'_v k_v=m_v. Tensoring the k_v and carrying identity on wire duals gives Z_N→Z'_N preserving global preparation/test legs. Standard CFS uniqueness then makes the span in §3 natural on this category of realizations of the fixed external cylinder.

Tensoring an M₀-arrow need not preserve M₀; there is no assertion that arbitrary comparison spans compose by pullback to give the canonical network span. The proved claims are the displayed naturality, raw flattening, and coherent NORMALIZED substitution.

An intervention replaces or attaches an explicitly supplied node arrow or boundary preparation/test. It is handled by the same derivation. The theorem does not claim that the physical correctness of an intervention is inferred from category theory.

## 5. Scope of the port-shaped hypothesis and an arrow specialization

The main theorem already applies directly to the port-shaped cylinders in §1 and needs no colimit/limit packaging. For another useful specialization, if a local cylinder r_v:D_v⇒T_v admits the relevant colimit I_v=colim D_v and limit O_v=lim T_v, then it induces an interface arrow f_v:I_v→O_v. Its CFS factorization legs induce maps

    I_v→R(r_v)→O_v

whose composite is f_v. Thus labelled local cylinder reconstructions provide the decorations needed by the theorem, **when these colimit/limit boundary objects and their proposed gluing have the intended operational meaning**.

This paragraph does not declare that every experimental context profile is such a physically glueable boundary, nor that every limit/colimit wire is dualizable. Those are concrete semantic checks for the chosen language. Alternatively the primitive arrows I_v→O_v may already be part of the specified interface model, as in matrix/kernel semantics.

The extra assumptions have consequently not been renamed “reconstruction preserves wiring.” They are explicit independent structure: local arrow interpretation, symmetric monoidal wiring, matched dualizable boundaries, and a CFS. Given them, the honest global factorization and comparison have been derived.

## 6. Relation to the quantale-module construction

For a commutative unital quantale V, complete V-modules form a symmetric monoidal category. The free boundary module V^B is self-dual:

    coev(1)=∨_b δ_b⊗δ_b,
    ev(δ_b⊗δ_c)=1 if b=c, and 0 otherwise.

Join-distributivity proves both snake equations on the free generators. Thus arbitrary (possibly infinite) free boundary sets are allowed within the chosen universe. With W=V^Z for the set Z of internal label assignments,

    Z_N=(⊗_v M_v)⊗V^Z ≅ ⊕_(z∈Z) ⊗_v M_v.

The cup/cap construction expands exactly to the witness-indexed formulas in `quantale_module_joint_wiring.md`. Its CFS span is therefore an instance of this general theorem, while its explicit image(h) formula supplies a particularly concrete normalized serial composition.

For Boolean V, this is support/constraint semantics. The complete module includes formal joins and may be large; those joins are not automatically physically available preparations. No smallness or learnability theorem is included. Other categories need their own verification of CFS and dualizable boundary objects; for example, cartesian Set has very few dualizable objects, so this is not an automatic universal theorem for Set systems.

## 7. Feedback boundary and known status

The allowed cyclic operation here is the algebraic compact trace obtained by cups/caps, equivalently simultaneous matching of internal labels in the Boolean example. It is not automatically causal guarded recursion, least fixed-point iteration, stochastic feedback, or analytic convergence. A different admitted feedback doctrine would need its own witness-preserving factorization construction; this theorem should not be advertised as supplying it.

The compact string-diagram and trace machinery is standard (Joyal–Street–Verity, [*Traced monoidal categories*](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/abs/traced-monoidal-categories/2BE85628D269D9FABAB41B6364E117C8)); the CFS infrastructure is standard (Garner, [*The Isbell monad*](https://arxiv.org/abs/1410.7108)). The displayed factorization is the elementary cup/cap construction, followed by orthogonality. No novelty is claimed. The substantive outcome for the present target is a proved route from specified local decorated reconstructions and an independent operational wiring law to an honest realization of the actual joint cylinder, and hence to a coherent canonical reconstruction comparison—without demanding that wiring preserve E and M.
