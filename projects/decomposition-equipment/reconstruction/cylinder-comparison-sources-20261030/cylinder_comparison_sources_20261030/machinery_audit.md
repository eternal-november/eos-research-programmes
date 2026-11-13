# Cylinder reconstruction/wiring: bounded machinery audit

Status: standard imports plus an elementary general comparison lemma; no novelty claim and no claim to have derived adequacy of an unknown wiring interface.

## 1. Exact known one-sided result

Garner, *The Isbell monad*, [primary preprint](https://arxiv.org/pdf/1410.7108), Definition 2.5, Theorems 4.1, 5.1 and 6.1: CFS has cylinder-factorized categories, class-preserving functors and arbitrary natural transformations. It is biequivalent to Isbell pseudoalgebras. Write A:IC→C and B:ID→D for reconstruction. M-preserving F:C→D corresponds to a coherent lax cell

    B IF ⇒ F A,

whereas E-preserving F gives a coherent colax cell in the reverse direction. Both classes give an invertible cell. Restricted shapes use saturated classes of weights; arbitrary finite lists of experiments are not automatically such a class. This already settles direction and coherence for one-sided preservation, but does not establish that physical/contextual wiring has that preservation property.

For one cylinder r=q e with middle V, factor Fr=e' followed by m' with middle V'. If F preserves M, orthogonality gives V'→FV; if F preserves E it gives FV→V'. This is the elementary component description of the above cells.

## 2. General comparison WITHOUT either preservation assumption

Here is a direct derivation, not a claimed literature novelty. Let C have a cylinder factorization system (E,M), and denote its underlying arrow classes by (E₀,M₀). Fix an actual cylinder r:D⇒T, with canonical factorization

    D --e_r--> R(r) --m_r--> T.

Suppose X is **any honest realization of that same cylinder**:

    D --p--> X --q--> T,       q p=r.

There are no generating/separating hypotheses on p,q. Factor the cocone p, considered as a cylinder with singleton target, and then factor the restricted observation cone:

    D --e--> U --m--> X,       e∈E, m∈M₀,
    U --a--> V --b--> T,       a∈E₀, b∈M.

The composite a e is in E. Proof: solve a lifting problem against an M-cone in two stages, first using e and then a; uniqueness also follows in two stages. Consequently b(ae)=r is a cylinder factorization, so V is canonically isomorphic to R(r). We obtain

    X <--m-- U --a--> R(r).

This is an (M₀,E₀)-span, whether or not wiring preserves either class. Only when M₀ consists of monos and E₀ consists of quotient maps is “subquotient” literally justified. In the usual regular epi/mono doctrine this is exactly the generated subobject followed by its observation image.

Applying this with X=F(R(r₀)) and p=F(e₀), q=F(m₀) always compares F(R(r₀)) with R(Fr₀). But operational wiring often changes preparations/tests or imposes correlations: then its actual cylinder need not be Fr₀. The genuinely missing premise is an actual realization of the correct external cylinder, not both-class preservation.

### Natural, but only in a precise category

Define Fact(r): objects (X,p,q) with qp=r; arrows h:X→X' satisfying hp=p' and q'h=q. Let U(X) be the first factorization middle above. Orthogonality of e_X and m_X' supplies the unique map U(h) with

    U(h)e_X=e_X',    m_X' U(h)=h m_X.

It preserves identities and composites by uniqueness. Moreover the maps a_X:U(X)→R(r) satisfy a_X' U(h)=a_X, by the lifting uniqueness for e_X against m_r. Thus there is a natural span of functors

    underlying : Fact(r)→C  <--m-- U --a--> constant(R(r)).

This gives genuine coherence for realization morphisms at a fixed cylinder. It is NOT a proof of coherence under arbitrary context substitution; that first requires a specified action on the relevant Fact(r)'s.

## 3. Explicit span/relational targets and their limits

In a regular category C, the wide subcategory of Span(C) whose arrows are spans X←U→Y with left leg mono and right leg regular epi is closed under pullback composition. Indeed, pulling back U→Y along V↪Y makes the new projection onto V a regular epi and the projection into U a mono. Composing the outside legs preserves their classes. Isomorphism classes of these spans form a category of partial surjections; before taking classes they form a bicategory with the inherited pullback associators.

This proves **composition of comparison spans is available**. It does not prove the composite is the canonical comparison for the externally composed wiring: a new context may access distinctions discarded earlier. Nor does arbitrary pullback composition of two record spans preserve realizability by a common raw preparation. Compatible intermediate records can have no jointly realizable raw witness.

For nonfunctional comparisons use Rel(C): objects of C, horizontal arrows subobjects of X×Y, composition the regular image of the pullback over Y, and 2-cells inclusions. This is concrete, not an unspecified “equipment.” It permits a finite positive witness and an infinite canonical realization to be compared via a relation in a semantic doctrine without requiring a positive map directly between them. A relation must still be shown to preserve the allowed preparation/test behavior; mere existence of a relation is vacuous.

Primary background: Carboni–Kasangian–Street, *Bicategories of spans and relations*, [publisher](https://www.sciencedirect.com/science/article/pii/0022404984900616), explicitly treats Span(E) for pullback categories and Rel(E) for regular categories. The partial-surjection closure argument above is provided here, not attributed as a theorem newly located in that paper.

## 4. Context-indexed/descent machinery does not supply missing physics

For a commuting context square

    A --h--> B
    |k       |g
    v        v
    C --f--> D,

a bifibration with adjoints u_! ⊣ u* has a canonical mate

    k_! h* ⇒ f* g_!.

Its construction is unit, reindexing isomorphism, then counit. Invertibility is an additional Beck–Chevalley property, not a consequence of drawing a pullback square in an arbitrary indexed semantics. Noninvertible mates remain useful comparisons; one should not demand universal BC invertibility merely because an exact/relational mission needs less.

Shulman, *Framed bicategories and monoidal fibrations*, [primary v2](https://arxiv.org/pdf/0706.1286), Definition 13.21, Lemma 16.1 and Theorem 14.4, provides the precise framed-bicategory infrastructure. It constructs compositional horizontal semantics from suitably BC monoidal bifibrations. Horizontal arrows need not be representable. Sections 16–17 locate where BC supports composition/unit coherence. This is infrastructure, not a theorem that local observational reconstruction descends through a proposed experimental context language.

For a typed multi-input wiring, a legitimate concrete starting point is a colored multicategory O of **declared** operations with functors W_w:∏C_ai→C_b and substitution constraints. It remains necessary to construct its action on actual cylinders/realizations, or on horizontal relations in a double category, respecting those constraints. Garner supplies comparisons after the relevant one-sided facts are proved. The lemma in §2 supplies a span once behavior factorization is proved. Neither infers undeclared operations or a complete grammar from finite data.

## 5. The real outstanding obligation

The lowest useful target is therefore NOT “prove every wiring preserves E and M.” It is:

1. Specify only the operational contexts under study and their actual cylinder semantics.
2. Derive for each such wiring a behavior-compatible candidate factorization, or a behavior-compatible relation in a specified semantic doctrine.
3. Prove compatibility under the substitutions actually used; retain the resulting directed comparison, span or relation when invertibility fails.
4. Establish any additional exactness/finite-sufficiency claim from independent structure (local port equations, causal closure, positivity-compatible simulation, known interaction laws), rather than renaming the desired semantic descent as an assumption.

The abstract span theorem means failure of generation/separation after wiring is not itself the obstruction. Failure to descend the actual context-sensitive observations through the local reconstructed interfaces is. That obligation is already solved for the supplied linear open-port example, but is unresolved for a general two-sided contextual programme or arbitrary positive finite witnesses. No novelty conclusion is supported by this bounded audit.
