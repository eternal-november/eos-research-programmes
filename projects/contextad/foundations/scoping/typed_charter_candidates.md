# Typed charter candidates for the first contextad scoping obligation

Status: proposed scope, not adopted theorem assumptions. Prepared 1 November 2026. The programme is generalizing contextads. Dependent mixed composition is the provisional first workstream; robots and recovery are only one application. This note makes a mixed arrow and its missing interaction fully typed, then tests one tempting source of that interaction. It does not claim novelty or a completed generalized contextad.

## 1. Common base and existing inputs

Start with a small category C, or a size-controlled category in fixed universes. For the first charter, ordinary categories with pseudofunctorial indexed structure suffice; higher ambient extension is not automatically included.

Let K be a contextad with fibration p:K→C and extension e:K→C. Write K_A for the fibre and eP=A⊙P for P∈K_A. For u:A→B, a cleavage supplies u*P and its cartesian extension map e(u*P)→eP. K has unit I_A and counit ε_A:eI_A→A. If P∈K_A and R∈K_{eP}, denote their combination by Kcomb(P,R)∈K_A and its structural map by

    δ_(P,R):e(Kcomb(P,R))→eR.

The target eR already includes its base eP. This notation avoids suppressing the dependent base.

Let L be a contentad with opfibration q:L→C and content extension d:L→C. For Q∈L_B write dQ=Q⊙B. A cleavage supplies u!Q and its cocartesian extension map dQ→d(u!Q) for u:B→B'. L has unit J_B and η_B:B→dJ_B. If S∈L_C and U∈L_{dS}, denote the combination by Lcomb(U,S)∈L_C and its structural map by

    μ_(U,S):dU→d(Lcomb(U,S)).

This agrees with the typing of contentful composition (Capucci–Myers Eq6.1.8). The prose order around Eq6.1.4 should not be copied without tracking bases. Both K and L include their existing unit, associativity and cartesian/opcartesian compatibility data. None of these one-sided structures supplies the mixed interaction below.

Primary source: Capucci–Myers, Definitions3.15/3.26, Examples3.20–3.24, Definitions6.2–6.3 and Eq6.1.8, https://arxiv.org/pdf/2410.21889 . Definition6.2 places contentads in a different, dual span/EM ambient construction; one cannot simply insert K and L as two monads in one tricategory without supplying that identification.

## 2. Mixed arrows, squares and pure maps

A proposed mixed arrow A⇒B is exactly

    (P,Q,f), with P∈K_A, Q∈L_B, f:eP→dQ in C.

Thus Q is over the *target B*, not over the unextended input or an unspecified sampled result. The subsequent dependence will be generated at composition.

A square with vertical maps a:A→A' and b:B→B' consists of a K-arrow φ:P→P' above a and an L-arrow ψ:Q→Q' above b satisfying

    dψ ∘ f = f' ∘ eφ.

These squares and their vertical composition are already typed. Equivalently, using the cleavages, the grade maps are φ:P→a*P′ in K_A and ψ:b!Q→Q′ in L_B′, followed by the chosen cartesian/cocartesian comparison maps. The directions agree with CM Definition3.17, Eqs3.3.15–16 (p22), and the contentful direction in Section6/Example6.4 (p65). Horizontal composition of them is one of the research obligations, not yet a theorem.

A pure map u:A→B has candidate horizontal representative

    (I_A,J_B, η_B ∘ u ∘ ε_A).

The vertical/tight category can remain literally C. The horizontal pure representative need not be faithful for arbitrary G/T-type specializations; faithfulness must not be silently inferred. Identity comparison and its coherence are part of the mixed unit law.

Use unquotiented presentations and squares initially. Reassociation may be a specified coherent isomorphism. Do not identify presentations merely because their visible output laws agree. Any extensional quotient gets a separate functor and its own preservation theorem.

## 3. The exact crossing data needed for binary composition

Take consecutive arrows

    (P,Q,f):A⇒B,       (R,S,g):B⇒C.

Here f:eP→dQ and g:eR→dS. Neither reindexing R along f nor pushing Q along g is directly typed: f lands in dQ, not B; g begins at eR, not B.

A candidate mixed crossing at the middle object is data

    Rhat(Q,R)∈K_{dQ},
    Qhat(Q,R)∈L_{eR},
    χ_(Q,R):e(Rhat(Q,R))→d(Qhat(Q,R)).

This is the exact missing interface. Define

    Pnew = Kcomb(P, f*Rhat),
    Qnew = Lcomb(g!Qhat, S).

The composite underlying map is the typed chain

    ePnew --δ--> e(f*Rhat)
            --cartesian extension above f--> eRhat
            --χ--> dQhat
            --cocartesian extension above g--> d(g!Qhat)
            --μ--> dQnew.

The whole binary operation therefore has the original mixed shape (Pnew,Qnew,composite):A⇒C.

At a minimum crossing must act on pairs of K/L arrows over the same base map: a pair (ψ:Q→Q', φ:R→R') over b induces a K-map Rhat→Rhat' over dψ and an L-map Qhat→Qhat' over eφ, with the corresponding χ-square commuting. Compatibility with the chosen cartesian/cocartesian transports is also required. A naive functor on object fibres alone does not establish horizontal square composition.

### What remains missing

To turn the typed recipe into coherent composition, prove or supply: crossing naturality; both one-sided unit interactions; interaction with K's dependent combination; interaction with L's dependent combination; and their compatibility with cleavage/transport and the one-sided associators. These are the dependent counterparts of the mixed-law diagrams. Merely naming them an interchange law is not a compatibility criterion.

For the singleton-fibre specializations eA=GA and dB=TB, χ is exactly GTB→TGB. The formula reduces to

    μ_C ∘ T(g) ∘ χ_B ∘ G(f) ∘ δ_A.

This correctly recovers the fixed comonad/monad control. But Street's mixed opwreath theory is a *stronger* generic baseline: it already allows effectful duplication G→TGG and deletion G→T. Therefore effects in those structure maps cannot themselves be advertised as the new result. See mixed_baselines.md for directly checked theorem/source locators.

## 4. Candidate independent source: display/codisplay factorization

Take a category C with a pullback-stable display class D and a pushout-stable codisplay class E, including identities and closed under composition. Contexts are D-maps r:X→A; content objects are E-maps c:B→Y. Then e(r)=X and d(c)=Y. This recovers the standard span and cospan contextad/contentad examples (CM Examples3.21–3.22 and6.6).

Mixed arrows are diagrams

    A ←r X →f Y ←c B,       r∈D, c∈E.

For a middle display s:U→B and codisplay c:B→Y, suppose the composite c∘s admits a factorization

    U --c'--> W --r'--> Y,       c'∈E, r'∈D.

Then Rhat is r', Qhat is c', and χ=id_W. Composing with a second mixed diagram B←s U→g V←d C gives:

    domain apex X×_Y W,
    output apex W+_U V,
    map X×_Y W→W→W+_U V,
    target codisplay C→V→W+_U V.

This construction uses three independently recognizable ingredients: factorization, pullback and pushout. Their bare existence and individual stability do **not** suffice for the whole mixed coherence theorem.

Unique or iso-unique factorization already has a known distributive-law theory (Rosebrugh–Wood; Lack). The potential increment would concern the *additional* pullback/pushout–factorization interaction required here, appropriate 2-cells and maps of examples, and the precise relation to the general mixed construction. It must not restate the known factorization crossing as new. An exact source-overlap decision is part of the audit, not settled by this candidate.

## 5. Finite associativity countercheck: regular epi/mono is insufficient

The tempting specialization C=FinSet, E=surjections, D=injections gives a normal form consisting of a partial function into a quotient of its target. Use image factorization for c∘s, ordinary pullbacks and pushouts. Both classes have the individual stability properties just listed, and factorization is unique up to unique isomorphism. Nevertheless this full mixed recipe is not associative.

Let A={a0,a1}, B={b0,b1,b2,b3}, C={c0,c1,c2}, D={*}.

First arrow f:A⇒B has full domain, quotient q:B→{q0,q1} with q(b0)=q(b1)=q0 and q(b2)=q(b3)=q1, and run(a0)=q0, run(a1)=q1.

Second arrow g:B⇒C has full domain and identity target quotient, with

    g(b0)=c0, g(b1)=c1, g(b2)=c1, g(b3)=c2.

Third arrow h:C⇒D has domain {c2}, run(c2)=*, and identity target quotient.

Compose f then g. The first crossing has W={q0,q1}; its pushout with g identifies c0 with c1 because b0,b1 share q0, and c1 with c2 because b2,b3 share q1. Consequently all C is identified. Both a0,a1 remain in the domain and map to that common quotient point. Composing with h then admits both a0 and a1, because the image of {c2} in this quotient is the entire one-point quotient.

In the other bracketing, g then h has domain exactly {b3}. Crossing this domain with q gives W={q1}. Pulling this subobject back along the first run admits only a1. Thus

    domain((f then g) then h) = {a0,a1},
    domain(f then (g then h)) = {a1}.

These presented arrows cannot be isomorphic over A: their domain legs have different images. The failure is therefore stronger than a different choice of pushout representative. The exact checker check_factorization_crossing.py validates all maps, performs finite union-find pushouts and image pullbacks, and asserts this mismatch. This is a diagnostic for this recipe, not a general no-go theorem or a novelty claim.

Interpretation: ordinary factorization coherence does not imply compatibility with the two other universal constructions. A proposed theorem requiring only regular epi/mono plus pushouts would be false. The missing interchange hypothesis must exclude this example by a structural reason, not by defining good data as data for which the desired associator exists.

A possible explanatory route is that these FinSet normal forms describe special (difunctional) relations and composition may leave that class. Broad exact/Mal'cev claims remain leads, not imported theorems here. The positive abelian/linear relation direction is already a strong known baseline: Fong–Zanasi, Universal Constructions for (Co)Relations, arXiv:1710.03894, Corollary3.4 and Section4.7, relate abelian corelations and relations and treat linear relations. The accompanying factorization ledger records inspection of the hypotheses, the Corollary3.4 proof and the main pushout theorem proof. Merely replacing FinSet by vector spaces and recovering standard linear-relation composition would not supply a new result.

A possible restricted repair to investigate is saturation of admitted later domains under produced quotients, with a closure theorem under the retained pure maps and pushforwards. Saturation must not be asserted sufficient before that check. Likewise FinSet is adhesive, but the quotient pushouts in this recipe are not the mono pushouts controlled by the usual adhesive axiom; invoking adhesiveness alone does not repair the example.

### A precise cell/presentation loss to compare, not a novelty marker

For the mono/surjection normal form, a fixed-endpoint square consists of domain inclusion X⊆X′ and quotient-coarsening ψ:Y→Y′ with ψ∘c=c′ and ψ∘f=f′|X. Passing merely to the underlying relation R={(a,b):a∈X and f(a)=c(b)} can lose content distinctions on unused quotient classes. For example let A={a}, B={0,1,2}, domain=A and f(a) the class {0}. The partitions {0}|{1}|{2} and {0}|{1,2} give the same relation {(a,0)}, but the noninvertible content-coarsening square between them is part of the presented data; the reverse quotient map does not exist. Thus a comparison identifying these presentations loses a specified noninvertible cell distinction, not just an informal notion of history. This does not establish that retaining this distinction is desirable or new, or that a relation/equipment formulation cannot retain it. Existing double-category/equipment comparison must be audited before using cell retention as the claimed increment. In particular proof-inspected double-categorical recognition is already available in Štěpán, arXiv:2504.04467, Theorems3.3.7 and3.3.33, for specified codomain-discrete/factorization double categories and strict/orthogonal factorization systems. Its square-preserving equivalences and strong corner/bicartesian/flatness hypotheses must be compared explicitly; a general appeal to retaining double cells is not a remaining gap.

## 6. Continuations, applications and dependency distinctions

For the abstract arrow class, the initially allowed continuations are all well-typed mixed arrows. This is a mathematical class, not a claim that every represented action is physically executable. A restricted observation-adapted or permission-aware substructure needs its own closure proof and is not silently assumed here.

Adaptive probabilistic programs test dependence on a *realized result*: the later context can vary over a sampled output while joint sample information is preserved. This is not equivalent to permitting an arbitrary dependent type over a whole probability distribution. Vákár's dCBPV-dependent Kleisli extension requires the latter kind of extension along a monadic unit and has strong known obstructions. Likewise Atkey's parameterized effects already allow changing state-object indices, but an output index fixed per arrow is not an arbitrary result-indexed fibre. See dependent-effect audit for precise references.

Typed protocols with dynamic capabilities test a deterministic result-indexed requirement: a returned handle, response tag or resource configuration determines subsequent legal operations. Ordinary state, session types and indexed effects are controls. Merely packaging the entire protocol into a large state object does not show the requested structural comparison or recognition criterion; conversely such packaging is not ruled out by definitional fiat.

Neither example is yet proved to instantiate the proposed crossing. The scoping deliverable must say whether the candidate class supports them and what is added to do so. The FinSet image-factorization test already shows that one attractive common setting cannot simply be declared positive. Robotics adds observation/physical-realizability and recovery pressures, but those are not mandatory axioms of all applications.

## 7. Proposed gate decision and assumption ledger

Recommend retaining the fully typed abstract crossing interface as the provisional target language, while **not freezing a positive class yet**. Candidate setting A uses arbitrary fibred/cofibred context/content data and seeks a derived crossing; candidate B uses display/codisplay normal forms and independently specified factorization. B is a concrete diagnostic and possible restricted theorem class, not established as adequate or novel. An audit can legitimately conclude that B is routine, false under weak hypotheses, or insufficient for the desired applications; acceptance of the first gate remains a user decision.

The smallest meaningful eventual theorem would derive the crossing and its full dependent coherence for a declared, nontrivial class from independently checkable data; prove the mixed construction and comparison maps; and establish a limited necessity or recognition statement. It must state its increment over Street's mixed opwreaths and existing factorization/span/cospan results. Merely supplying χ and all its required diagrams meets typing but not the scientific criterion.

Assumption roles:

- Smallness/universes: size/typing hygiene.
- Given contextad K and contentad L: existing input structures, with their one-sided coherence supplied and audited.
- Cleavages: choosing presentations of reindexing/pushforward; comparison under alternative choices must be stated.
- χ with its fibres and action on squares: missing mixed data. Not automatically supplied by K,L.
- Mixed unit and multiplication compatibilities: either derived from the proposed independent structure or explicitly supplied; cannot be counted as a derived compatibility criterion when assumed wholesale.
- In the display/codisplay candidate, pullbacks/pushouts and class stability: construction/typing.
- Chosen factorization with uniqueness: constructs χ and may derive its own naturality/coherence, but does not settle PB/PO interchange.
- Further exactness/interchange property: unresolved. It must have an independently meaningful formulation and verified examples.
- Quotient/output-law comparison: optional additional construction with separately declared strength; not part of equality of raw mixed arrows.
- Observation or physical availability: application data, not consequences of categorical representability.

No global disintegration, arbitrary conditional sampler, universal undo, full higher-order language, all feedback or ambient noncartesian extension is used to make this charter type-check. No theorem hypotheses are frozen by this note.
