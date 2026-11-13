# Explicit instances and internal constructors for the common cell-rich construction

## 0. Convention and the exact claim being made

The common carrier is a bicategory H with the same objects as a specified ordinary pure category C, together with an identity-on-objects pseudofunctor J:C→H. Equivalently, use the Cat-valued relative-matrix/pseudopromonad presentation developed in `common_ambient.md` and `mixed_factory.md`. Tensor is written left-to-right. The induced two-sided C-action on H(A,B) is pure whiskering; it is generally pseudofunctorial, not strict.

Its associated double category has tight arrows u in C, loose arrows h in H, and endpoint squares

    J(v) ∘ h  ⇒  h' ∘ J(u).

Native endpoint squares below have precisely this orientation. All ordinary parameter maps are retained as morphisms in hom categories, including noninvertible and distinct parallel maps. No isomorphism-class quotient is implicit.

“Recovery” below concerns the operational category/bicategory and its endpoint squares. Unless marked canonical arrows/extension data are retained, it does NOT claim that H,J intrinsically reconstruct the original grading K, L, or a chosen display presentation. Likewise J need not be faithful. The structured base C is fixed within an instance, but constructors such as indexed Grothendieck extension change the base and come with explicit comparison functors.

## 1. Ordinary effects are literal locally discrete instances

Let C be ordinary, T a monad and G a comonad.

### Monad

    H_T(A,B) = disc C(A,TB),
    g ⋆ f = μ_C T(g) f,
    J_T(u) = η_B u.

The native endpoint square over u:A→A', v:B→B' exists precisely when

    T(v)f = f'u.

Thus the associated double category is the usual Kleisli square double category, by a literal identity on objects, pure arrows, loose arrows and squares. Its cells are discrete at fixed endpoints because C is ordinary; no existing nontrivial cells have been discarded.

### Comonad

    H_G(A,B) = disc C(GA,B),
    g ⋆ f = g G(f) δ_A,
    J_G(u) = u ε_A.

An endpoint square exists precisely when vf=f'G(u). Recovery is again literal. These are also the singleton-fibre Cnt and Ctx cases, respectively, with d_B(*)=TB and e_A(*)=GA. Singleton fibres do not force η, μ, ε, δ to be invertible.

Neither pure embedding need be faithful: for example the terminal monad on Set identifies all pure maps having the same source and target. Therefore no theorem about the common carrier may assume faithful pure maps without an additional hypothesis.

## 2. General Ctx and Cnt are non-discrete instances

### Ctx

Take a contextad with indexed category K:C^op→Cat, extension e:∫K→C, unit I_A, discharge ε_A:e_AI_A→A, and accumulation

    P⊗R ∈ K_A,       R∈K_(e_AP),
    δ_(P,R):e_A(P⊗R)→e_(e_AP)R.

Put

    H_K(A,B) = (e_A ↓ B).

Objects are (P,f:e_AP→B). A morphism (P,f)→(P',f') is α:P→P' with f=f'e_Aα. Compose (P,f) and (Q,g) with grade P⊗f*Q and body

    e_A(P⊗f*Q) --δ--> e_(e_AP)(f*Q)
      --extended cartesian lift over f--> e_BQ --g--> C.

The unit is (I_A,ε_A); J_K(u)=(I_A,uε_A). The contextad coherence is exactly what makes these operations a bicategory rather than merely a collection of comma categories. A general square is α:P→u*P' satisfying

    vf = f' e(u,α).

The chosen companion construction bends this square to J(v)∘(P,f)⇒(P',f')∘J(u), and unbends it back. Consequently the native Ctx pseudo double category is recovered by an identity-on-tight-data double equivalence (up to chosen unit/composition constraints), with an isomorphism of each native square set. This is stronger than recovering its ordinary horizontal category, but weaker than an intrinsic recognition theorem for K from H alone.

### Cnt

Take L:C→Cat with extension d, unit J_A and insertion η_A:A→d_AJ_A. Define the ordered accumulation

    Q◇S ∈ L_A,       S∈L_(d_AQ),
    μ_(Q,S):d_(d_AQ)S→d_A(Q◇S).

Put H_L(A,B)=(A↓d_B). An object is (Q,f:A→d_BQ); a morphism is β:Q→Q' with d_Bβ f=f'. For (Q,f):A⇒B followed by (S,g):B⇒C, the grade is

    S◇g!Q,

and the body is f, extension along g, then μ. J_L(u)=(J_B,η_Bu). A native endpoint square has β:v!Q→Q' with

    d_B'(β) d(v,Q) f = f'u.

The same bending argument recovers every native square. Neither within-fibre cell direction has been reversed: both α and β point forward. Contravariance of K refers only to change of base.

### Direct companion check for Cnt

This does not rely on applying the contextad companion theorem without dualizing it. For u:A→B choose the contentful companion J_L(u)=(J_B,η_Bu). Its first companion square, from the loose identity at A to J_L(u) with vertical sides id_A,u, uses the coherent unit transport isomorphism u!J_A→J_B. The square equation is precisely naturality of η. Its second square, from J_L(u) to the loose identity at B with vertical sides u,id_B, uses id_(J_B). The two companion identities are the unit transport/unit-composition axioms. Equivalently, composing a native F with J(v) identifies its grade coherently with v!Q, while composing F' after J(u) identifies its grade with Q'; the globular cell is exactly β:v!Q→Q'. This verifies that the companion-bending reconstruction applies to native Cnt as well as native Ctx.

### Marked presentation recovery

The operational carrier can retain more than H,J by marking the expansion arrows

    κ_P=(P,id_(e_AP)):A⇒e_AP

and their native squares. Form a category whose objects are these marked expansions and whose arrows are their endpoint squares, allowing both endpoints to vary. A square κ_P→κ_P' over u:A→A', v:e_AP→e_A'P' is α:P→u*P', and its equation forces v=e(u,α). Thus this category is (canonically, in the chosen split notation) the total category ∫K; the source projection recovers its fibration, the target projection recovers e, and marking cartesian lifts recovers the chosen cleavage. Every (P,f) is κ_P followed by J(f), through the specified unit comparison.

For P∈K_A and R∈K_(e_AP), κ_R∘κ_P is (P⊗R,δ_(P,R)); hence the marked factorization through κ_(P⊗R) followed by J(δ_(P,R)) retains the accumulation comparison rather than incorrectly identifying this composite with the expansion alone. Marking the unit grade similarly retains ε. This is a recovery of supplied marked presentation data, not a theorem that unmarked H,J uniquely selects it.

Dually mark the generic content arrows γ_Q=(Q,id_(d_BQ)):d_BQ⇒B. A square γ_Q→γ_Q' over r:d_BQ→d_B'Q' and v:B→B' is β:v!Q→Q', and its equation forces r=d_B'(β)d(v,Q). Thus the category of marked generic arrows recovers ∫L with its opfibration and extension. A general (Q,f) is J(f) followed by γ_Q; marked composite generic arrows retain μ.

Morphisms between these constructed objects need not all be strong: a lax comparison can retain a noninvertible structural comparison as part of its data. Such lax comparison functors must be kept distinct from equivalences or strong pure-compatible morphisms. Allowing them does not weaken the associativity/unit coherence required of the underlying object H.

## 3. Para and spans inside those same hom categories

### Right monoidal actions / Para

Let a monoidal category V act on C on the right, with A⊙P and coherent isomorphisms A⊙(P⊗Q)≅(A⊙P)⊙Q. Take K_A=V, constant reindexing, e_AP=A⊙P. Then

    H(A,B): objects (P,f:A⊙P→B),
    morphisms α:P→P' with f=f'(1_A⊙α).

Composition has parameter P⊗Q and body the action comparison, f⊙1_Q, then g. The unit parameter is the monoidal unit. A changing-endpoint square is exactly

    vf=f'(u⊙α).

This recovers the forward-reparametrization convention for Para, including all parameter maps. Sources that define Para with reverse reparametrizations use a different cell convention and require the corresponding opposite; they are not literally identical. V need not be cartesian, and nothing here installs copying of a general parameter.

### Display spans

Let D be a class of maps in C containing identities, closed under composition and stable under chosen pullbacks. Set K_A=D/A, with morphisms all commuting maps over A, and extension the domain. Then H(A,B) is precisely the category of spans

    A ←p X →f B,       p∈D,

with apex maps. Composite apex is X×_B Y; left leg is p composed with its pullback projection. The pure map u is A←id A→u B. A square over (u,v) is an apex map a:X→X' satisfying p'a=up and f'a=vf. Thus the common construction recovers the display-span double category, not just spans modulo apex isomorphism.

With chosen pullbacks, coherence is canonical rather than necessarily strict. Dual pushout-stable codisplays give cospans with designated right leg, via Cnt. No compatibility between the span and cospan halves is supplied merely by having both instances; their mixed normal-form law remains extra data.

## 4. Mixed laws and opwreaths are operations inside the carrier, with different inputs

### A separately supplied comonad and monad

For λ:GT⇒TG satisfying the four mixed law axioms,

    H_(G,T,λ)(A,B)=disc C(GA,TB),
    g ⋆ f = μ_C T(g) λ_B G(f) δ_A,
    1_A=η_Aε_A,
    J(u)=η_Buε_A.

Endpoint squares are Tv f=f'Gu. This is the fixed-effect specialization of the relative mixed product. The one-sided comparison functors send coKleisli f to ηf, and Kleisli g to gε. They preserve units and composition by the law axioms. They are NOT automatically faithful or fully faithful: η may identify arrows and precomposition by ε may do so too. In particular, a terminal T can collapse the entire comonadic hom set. Therefore “recover the one-sided cases” means specialization to the trivial opposite effect, or the specified comparison functors; conservativity for a nontrivial partner must be separately proved.

### Mixed opwreath

Street's more general input consists of a monad T and G with

    ζ:GT⇒TG,    d:G⇒TGG,    e:G⇒T,

satisfying the seven opwreath axioms. It supplies the same hom objects C(GA,TB), but composition is

    GA --d--> TGGA --TGf--> TGTB --Tζ_B--> TTGB
       --TTg--> TTTC --μ^(3)--> TC,

and unit e_A. The pure map is J(u)=T(u)e_A=e_B G(u). The opwreath theorem gives its associativity and units; naturality gives the pure functor. This is a direct object of the common carrier. It need NOT arise by crossing a separately available coKleisli category for G, because G need not itself be a comonad. The distinction is substantive: effectful discharge and duplication are more general than a separate pure comonad.

For 2-categorical inputs the corresponding hom category is B(GA,TB), subject to the higher opwreath/two-sided Kleisli hypotheses and coherent constraints. This statement does not automatically embed every noncartesian higher ambient into the particular Set-indexed relative matrix setting: universe, enrichment, object and base choices must be supplied.

## 5. Grothendieck extension makes the presentations internal monad constructions

This section is an actual constructor/recovery theorem, not an analogy between contexts and monads.

Assume a split indexed presentation K and the contextad structure above, with size control. Work on the 2-category Psh(C) of Cat-valued presheaves, pseudonatural transformations and modifications. Define

    (P_K Y)(A) = ∫_(P∈K_A) Y(e_AP),

using the contravariant Grothendieck construction. Explicitly, a morphism (P,y)→(P',y') is

    (α:P→P', γ:y→Y(e_Aα)(y')).

Along u:A→B, reindex (P,y) to (u*P,Y(e(u,P))y). The unit sends y∈Y(A) to (I_A,Y(ε_A)y). The multiplication sends

    (P,(R,y)) ↦ (P⊗R,Y(δ_(P,R))y).

These formulas are well typed even when ε and δ are not isomorphisms. Naturality and contextad coherence give a pseudomonad. More structurally, the Grothendieck extension is a monoidal pseudofunctor from split left-fibrant spans with right-colax maps to endo-2-functors; monoids/pseudomonoids go to monads/pseudomonads. This is Kamiya Proposition 3.2, BEFORE the additional comprehension-equivalence assumption introduced in §3.2.

Let yA=C(-,A), viewed discretely. Then 2-Yoneda gives

    PsNat(yA,P_K yB) ≃ (P_K yB)(A) = H_K(A,B).

The right equality includes morphisms: γ in the discrete representable exists exactly when f=f'eα. Under the comparison, Kleisli composition is the contextad composition displayed in §2, and endpoint modifications are the native squares. Therefore the representable part of Kl(P_K), with pure maps transported along Yoneda, recovers Ctx(K) by a local equivalence preserving all cells and horizontal structure. This does not assert equivalence with the ENTIRE Kleisli bicategory, whose objects include arbitrary Cat-valued presheaves. Nor does it assert an unrestricted classification of all pseudomonads as such P_K.

### Covariant dual for contentads

For a split L, work on Copsh(C)=[C,Cat]. Define the covariant Grothendieck extension

    (Q_L Y)(B)=∫_(Q∈L_B) Y(d_BQ),

whose morphisms are (β:Q→Q', γ:Y(dβ)y→y'). Insertion and multiplication use Yη and Yμ, respectively, so this is again a pseudomonad. Write y^A=C(A,-). Then

    PsNat(y^B,Q_L y^A) ≃ (Q_L y^A)(B) = H_L(A,B).

Since A↦y^A is contravariant, Cnt(L) is recovered from the **1-cell-opposite** of this Kleisli bicategory restricted to corepresentables. Hom-category morphisms are not reversed. This dual explicit formula avoids silently changing native content-cell orientation.

### Telescopes

For a split left-fibrant span M, let M^⋉n be its n-fold sequential product and

    Tel(M)=coprod_(n≥0) M^⋉n.

The unit inserts length-one strings; multiplication flattens strings of strings. The fibres contain dependent finite chains, since the next grade is over the extension by the preceding grades, not merely a list in one fixed fibre. Monoidality and coproduct preservation give

    P_Tel(M) ≃ coprod_(n≥0) P_M^n.

Thus the telescope constructor lives inside the SAME extension mechanism as the contextad realization; it is the free monad construction in the applicable coproduct-preserving endofunctor setting. A contextad multiplication evaluates these words by its iterated accumulation. Strict Tel-algebras with the stated normal-cleavage/strict-map assumptions recover strict contextads (Kamiya Corollary 2.20); pseudo and transported versions require the specified coherence and equivalence hypotheses. An arbitrary fibrewise category is not thereby equivalent to a prescribed display class. That stronger identification requires the comprehension equivalence of Kamiya §3.2, and remains visible as an input.

## 6. A genuinely nonthin dependent instance of the mixed multiplication

Take C=Set, K_A=(Prob+)^A, where Prob+ has finite nonempty full-support normalized probability spaces and deterministic measure-preserving maps. Extend by e_AP=Σ_a P_a and accumulate by dependent pairs with product conditional weights. Take the singleton-fibre List contentad. Then

    H(A,B): objects (P,f:Σ_aP_a→List B),
    cells α:P→P' satisfying f'(a,α_ax)=f(a,x).

For endpoint maps (u,v), the condition is f'(u a,α_ax)=List(v)f(a,x). The crossing of a list [b_i] and a context family Q is the independent occurrence product

    Qhat_[b_i]=product_i Q_bi,
    χ([b_i],(y_i))=[(b_i,y_i)].

The word “occurrence” is indispensable: equal labels at different positions still receive different coordinates. This is the probability tensor on carriers, not a categorical product in Prob+.

For F=(P,f):A⇒B and G=(Q,g):B⇒C, write f(a,x)=[b_i]. Then

    (G⋆F).context_a = Σ_(x∈P_a) product_i Q_bi,
    weight(x,(y_i)) = p_a(x) product_i q_bi(y_i),
    (G⋆F).output(a,x,(y_i)) = concat_i g(b_i,y_i).

The horizontal composite of cells α,β is (x,(y_i))↦(αx,(β_bi y_i)). The square condition ensures the same occurrence count and target positions, including noninjective pure maps v. Measure preservation follows from the product-of-sums identity followed by summing over α-preimages.

For a third arrow the associator is the weight-preserving tuple bijection

    ((x,(y_i)),(z_ij)_flattened) ↔ (x,((y_i,(z_ij)_j))_i).

Variable list lengths cause no ambiguity: the output g(b_i,y_i) determines every inner block boundary. Pentagon, triangle and naturality hold because all routes preserve the same finite occurrence addresses and the same sample at every address. This proves coherence at the witness-map level, not only equality of probability distributions.

Its local mixed factorization is

    H(A,B) ≅ ∫^Z H_K(A,Z) × disc Set(Z,List B)

for the ordinary strict Cat-coend (the corresponding pseudo-relative comparison is handled in the common factory note). Composition agrees with the law from occurrence products. Singleton output lists recover Ctx(K); singleton probability contexts recover List Kleisli. Here, unlike arbitrary mixed laws, these inclusions ARE locally fully faithful: their native cell equations coincide exactly with the restricted mixed equations. Their horizontal structures agree by the displayed unit/tuple isomorphisms. This gives a full genuine instance of the common carrier and mixed multiplication, rather than just an ordinary stochastic quotient.

The pushforward-law map to the Kleisli category of finite distributions composed with List forgets witness presentations and their noninvertible maps. It is a further semantic comparison, not the construction itself. The proof and regression details are in `../contextad_harder_tests_20261101/nonthin_categorical_test.md`.

## 7. Reader/writer controls, with exact recovery level

For an environment E, the product comonad GA=E×A yields coKleisli arrows E×A→B with g⋆f(e,a)=g(e,f(e,a)). In Set (or with the required cartesian closed structure), currying identifies these with A→B^E, and the reader monad multiplies by using the same environment twice. This is an identity-on-objects isomorphism of ordinary categories. The endpoint equations also coincide under currying, hence the associated pure-square double categories are isomorphic. This does not assert an arbitrary nonthin Para-to-reader equivalence.

For a monoid W, the writer monad TA=W×A has arrows a↦(w(a),f(a)). Equivalently, use a discrete context fibre of functions w:A→W and extension A. Composition is

    (w,f);(v,g) = (a↦w(a)v(f(a)), g f).

The parameter condition over u is w=w' u; the body condition over v_base is v_base f=f'u. These are exactly the writer Kleisli endpoint equations. Hence this concrete transposition is an identity-on-objects/pure-arrows double-category isomorphism, not merely an arrow bijection.

The fixed mixed reader/writer law is

    E×(W×X)→W×(E×X),   (e,(w,x))↦(w,(e,x)).

Its four compatibility axioms reduce to monoid associativity/unit and duplicating/discarding E. It is an elementary control for §4, not evidence that arbitrary dependent crossings exist.

## 8. Factorization recognition: a marked sub-double category of the same ambient

There is an important companion boundary. A factorization double category with vertical class E and horizontal class M need not possess horizontal companions for every vertical arrow: an E-arrow need not belong to M. Consequently it cannot automatically be identified with a full relative-quintet construction Q_C(H,J). Instead the common construction realizes its companion-bearing envelope, with the original factorization double category recovered as a marked horizontal restriction.

Explicitly, let A be an ordinary category and E,M wide subcategories (same objects, containing identities, closed under composition). Regard A as a locally discrete bicategory and let J_E:E→A be the inclusion. Construct

    Q_E(A,J_E).

It has vertical arrows in E, horizontal arrows all of A, and a unique square with boundary (f:X→Y, g:X'→Y', u:X→X', v:Y→Y') exactly when

    v f = g u.

Now mark the horizontal arrows belonging to M, retaining every square whose top and bottom are so marked. Since M contains identities and is composition-closed, this defines a sub-double category

    D_(E,M)(A) ⊆ Q_E(A,J_E).

Its objects are Ob(A), tight arrows are E, loose arrows are M, and cells are precisely the commuting E/M squares. Both compositions are literal compositions/pastings in A. This is an isomorphism with the usual factorization double category attached to (A,E,M), not a quotient or merely an identification of its objects. All its cells survive. The envelope's companion of e∈E is the horizontal arrow e, which need not be in the marked sub-double category. Thus we have not incorrectly installed companions inside D_(E,M)(A).

Under the specific strict/orthogonal factorization recognition hypotheses, apply Štěpán's theorem to reconstruct A and its two classes, then use the displayed envelope-and-restriction construction. Factorization existence/uniqueness or orthogonality is then a property of the marked classes inside this single ambient instance, not another effect to be multiplied. Rosebrugh–Wood and Lack similarly turn suitable normal-form/factorization data into a distributive crossing. Their respective hypotheses remain necessary; the ambient does not produce normal forms by itself.

The enriched/nonflat situation requires further care. An arbitrary double category with multiple cells having the same boundary is not recovered by the locally discrete A construction above. A general double category without companions is likewise not covered by the companion-bending theorem merely because it has been called a factorization double category. One must either supply a suitable cell-rich companion completion with a proven conservative inclusion, or verify a recognition theorem whose hypotheses yield the particular envelope described above. No universal conservative completion theorem is being asserted here.

This placement is substantive rather than a list of unrelated theories: the marked classes, their factorization properties and their commuting squares inhabit one operational ambient, while the missing-companion boundary remains explicit. A candidate crossing can fail pure-middle balancing before associativity; a quotient can preserve output behavior while destroying factorization witnesses; a valid factorization theorem can supply the crossing when its hypotheses hold.

## 9. Scope and source status

The formulas above deliberately separate: (i) literal specialization; (ii) local equivalence with coherent double recovery; (iii) a specified possibly nonfaithful comparison; (iv) a recognition property requiring hypotheses. They do not claim automatic faithful amalgamation, automatic mixed laws, or recovery of chosen presentations from an unmarked operational bicategory.

Primary sources used: Capucci–Myers, *Contextads as Wreaths*, arXiv:2410.21889, especially Def.3.17, Ex.3.21, Thm.4.24 and §6; Street, *Wreaths, mixed wreaths and twisted coactions*, arXiv:1610.07281, Def.5/Prop.7; Kamiya, *The Grothendieck construction, telescopes and contextads*, October 2026, Construction3.1, Prop.3.2, Cor.2.20 and Prop.3.6 (local archived manuscript); Garner, arXiv:math/0606735, higher two-sided Kleisli; Štěpán thesis arXiv:2504.04467, Thms3.3.7/3.3.33; Rosebrugh–Wood, *Distributive laws and factorization*; Lack, *Composing PROPs*. The covariant Grothendieck contentad formula here is the explicit dual construction, not an attributed verbatim theorem from Kamiya. The concrete probability/List coherence argument is the earlier project proof, not a historical novelty claim.
