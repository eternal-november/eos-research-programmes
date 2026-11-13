# Internal interface retyping of witnessed squares

## Plain language summary

Changing the two hidden interface types of a witnessed square is not automatic. Each original whole witness acquires copies indexed by the new interface values. To lift the old whole matching, the copies on the two sides must be paired. Those pairings produce a genuine intermediate component exactly when they depend only on its intermediate witness, not on which surrounding left and right witnesses happen to expose it.

This gives an explicit mixed compatibility test. It also identifies the additional data required for a valid interface change and proves that compatible changes compose. It is not a claim that every pair of interface maps preserves a square filler.

## 1 Original data and separate restrictions

Use a fully visible square from ../witnesses/Witnessed_Square_Reconstruction.md:

    L:A↝B, R:C↝D, V:A↝C, W:B↝D,
    θ:V;R≅L;W,

with L_b and R_c nonempty for every b∈B,c∈C. Assume θ has a filler (U,α,β), so

    θ(α(l,u),r)=(l,β(u,r)).

Let f:B'→B and g:C'→C be any finite functions. Restrict the four boundary spans separately:

    L'={(l,b'):b_L(l)=f(b')}:A↝B',
    W'={(b',w):f(b')=b_W(w)}:B'↝D,
    V'={(v,c'):c_V(v)=g(c')}:A↝C',
    R'={(c',r):g(c')=c_R(r)}:C'↝D.

All L'_{b'} and R'_{c'} are still nonempty, so a lifted square remains fully visible. Let p_VR:V';R'→V;R and p_LW:L';W'→L;W forget the primed interface witness.

A lifted whole matching is a span isomorphism θ':V';R'≅L';W' satisfying

    p_LW θ' = θ p_VR.                                      (1)

Separate cartesian restrictions alone do not provide θ': they produce two different sets of copies of the whole matching.

## 2 The exact data needed to lift the whole

Every original whole witness can be written uniquely as (α(l,u),r), with a composable triple (l,u,r). Its fibre under p_VR is g^{-1}(c_U(u)); the corresponding fibre under p_LW is f^{-1}(b_U(u)). Therefore a θ' satisfying (1) is exactly a family of bijections

    λ_{l,u,r}:g^{-1}(c_U(u)) ≅ f^{-1}(b_U(u))               (2)

over all composable triples. Its formula is

    θ'((α(l,u),c'),(c',r))
      = ((l,λ_{l,u,r}(c')),
         (λ_{l,u,r}(c'),β(u,r))).                         (3)

Thus some lifted whole matching exists iff the two finite fibre cardinalities in (2) agree for every u. Because L_b and R_c are nonempty, this condition can be checked once per u, not only on an accidentally empty collection of triples. Empty fibres on both sides are allowed and have a unique bijection.

This existence statement concerns only a lifted whole matching, not yet a filler of that matching.

## 3 The mixed reconstruction criterion

### Theorem 1 Internal retyping criterion

For a specified lifted whole matching θ' represented by (2), the following are equivalent.

1. The retyped square (L',R',V',W',θ') has a filler.
2. For each original u∈U, the bijection λ_{l,u,r} is independent of both l∈L_{b_U(u)} and r∈R_{c_U(u)}. Write its common value λ_u.

When these conditions hold, a canonical new filler is

    U'={(u,c'):g(c')=c_U(u)}

with C' endpoint c' and B' endpoint λ_u(c'). Its isomorphisms are

    α'((l,λ_u(c')),(u,c'))=(α(l,u),c'),
    β'((u,c'),(c',r))=(λ_u(c'),β(u,r)).                    (4)

The solution groupoid for this fixed θ' is contractible.

#### Proof of necessity

Suppose a filler of θ' exists. The visible rectangle criterion implies that the left-edge label of every incidence edge depends only on its V' vertex, and the right-edge label depends only on its W' vertex.

Fix u,l,c'. At the V' vertex (α(l,u),c'), formula (3) says that the L' label is (l,λ_{l,u,r}(c')). Its independence from r gives

    λ_{l,u,r}=λ_{l,u,r'}

as functions, for all r,r'. Dually, fixing u,r,b' and using θ'^{-1} at (b',β(u,r)), independence of the R' label from l gives

    λ_{l,u,r}^{-1}=λ_{l',u,r}^{-1}

for every l,l'. These imply independence from both l and r. The argument remains valid for empty primed fibres, when all involved bijections are the unique empty map.

#### Proof of sufficiency

Use U' and (4). Given (v,c')∈V', write uniquely v=α(l,u). The unique preimage under α' is ((l,λ_u(c')),(u,c')). Thus α' is a typed bijection. Given (b',w)∈W', write uniquely w=β(u,r); the unique c'=λ_u^{-1}(b') gives the preimage under β'. Hence β' is a typed bijection. Formula (3) with λ_u verifies the filler coherence equation. Contractibility follows from the fully visible square theorem. ∎

### Corollary 2 Classification when the lifted matching is not prescribed

Fix f,g and the original square. The groupoid of pairs consisting of a lifted whole matching θ' over θ and a filler of θ', with θ' kept as part of the data and fixed by morphisms, is equivalent to the discrete set

    ∏_{u∈U} Bij(g^{-1}(c_U(u)), f^{-1}(b_U(u))).           (5)

It is empty if any required fibre cardinalities differ. If they agree, writing their common sizes n_u, the number of connected components is ∏_u n_u!. Distinct choices are distinct actual lifted matchings, not artificially attached labels. A fixed matching has a contractible filler fibre.

Proof. Theorem 1 says exactly which matching families (2) lift and gives one component for each constant-in-l,r family. Different λ_u differ on some c' and, since both original side fibres are nonempty, formula (3) distinguishes their actual θ'. ∎

## 4 Interpretation as a cartesian map on both span legs

The projection p:U'→U, (u,c')↦u, sits over f:B'→B and g:C'→C. Both squares formed with the two legs of U are pullback squares of finite sets:

- the C square is a pullback by the definition of U';
- the B square is a pullback because λ_u is a bijection between the g and f fibres for each u.

Conversely a span map p:U'→U over f,g whose two leg squares are pullbacks induces exactly such a family λ_u. Thus the mixed condition says that the lifted whole matching must descend to a simultaneous cartesian retyping of the actual hidden witness span.

This conclusion is derived from the witnessed coherence equation. It is not an assumption that the desired filler already exists.

## 5 Composition and coherence of valid internal retypings

Suppose a first valid change uses f:B'→B, g:C'→C and λ_u. Suppose a second uses f':B''→B', g':C''→C' and, for each intermediate witness (u,c'), a fibre bijection

    μ_{u,c'}:(g')^{-1}(c') ≅ (f')^{-1}(λ_u(c')).

The composite fibre bijection is

    Λ_u:(g g')^{-1}(c_U(u)) → (f f')^{-1}(b_U(u)),
    Λ_u(c'') = μ_{u,g'(c'')}(c'').                         (6)

It is bijective because the domain is partitioned by c'=g'(c''), the first λ_u bijects these c' values with the corresponding b' values, and each μ bijects the fibres over that pair. The two-stage filler has witnesses (u,c',c'') with c'=g'(c''); deleting the determined c' is a canonical isomorphism to the one-stage filler (u,c''). Under that isomorphism, the α and β formulas agree literally with those obtained from Λ_u.

Identity interface maps use singleton-fibre identities. For three successive changes, both routes send the final interface value through the same nested fibre functions; hence their associativity and unit comparisons satisfy the coherence equations on fully written tuples. This proves composition of valid internal retyping, not preservation under an arbitrary independent pair of interface restrictions.

## 6 Failure example and limits

Take a visible square with singleton outer and inner object sets, L=R={0,1}, U={*}, V=L, W=R, and θ(l,r)=(l,r). Let B'=C'={0,1}, with f,g the unique maps to the singleton. Choose

    λ_{l,*,r}(c')=c' XOR (l AND r).

Every λ is a bijection, so θ' is a valid whole matching over θ and all separate fibre cardinalities agree. But at l=1 its value depends on r. Theorem 1 therefore proves that the retyped square has no filler. This is a mixed witness obstruction created by an incoherent pairing of the separately retyped interfaces, not a failure of either individual restriction to exist.

The theorem assumes the original square is fully visible and already fillable. One-sided or doubly invisible original sectors require the tiling and automorphism data of the general square theorem; no automatic extension of the constant-λ criterion to those sectors is asserted. Inner object maps that are not functions, arbitrary changes to θ not lying over the old matching, and general networks of crossing squares are also outside this statement.

## 7 Mixed coherence with outer contexts

Let H:A'↝A and K:D↝D' be arbitrary finite outer spans. Their whiskering sends the original square to the square with boundaries H;L, R;K, H;V, W;K and whole matching

    (h,v,r,k) ↦ (h,l,w,k)  whenever θ(v,r)=(l,w).

It transports the chosen filler with the same U, as in the outer-context theorem of ../witnesses/Witnessed_Square_Reconstruction.md. Outer contexts may delete visible witnesses, so no assertion that the whiskered square remains fully visible is made.

### Theorem 3 Mixed transport coherence

A valid internal retyping (f,g,λ_u) and an arbitrary outer whiskering (H,K) commute through the canonical tuple-rebracketing bijections. Both orders produce the same intermediate witness set U'={(u,c')} and the same whole matching, written without suppressed associators as

    (h,α(l,u),c',r,k)
      ↦ (h,l,λ_u(c'),β(u,r),k).                         (7)

The resulting comparisons are natural in filler isomorphisms respecting the λ data and satisfy unit, associativity, and mixed interchange coherence for any finite sequence of these transport operations.

Proof. Restricting the B leg of H;L gives tuples (h,l,b'), canonically the same as H;L'; restricting the C leg of R;K gives tuples (c',r,k), canonically R';K. The analogous identities hold for H;V and W;K. Formula (4) then gives (7) regardless of the order of operations.

For two outer contexts, both associativity routes merely add and regroup the same outer tuple coordinates. For two internal changes, Section 5 shows both routes use the same composite fibre map (6). Mixed interchange changes neither the intermediate u nor the c' value to which λ_u is applied, because λ_u is independent of every outer witness. Thus every coherence diagram compares functions with literally identical values on fully written tuples.

For naturality, a filler isomorphism γ:U→Ũ compatible with the matching data, meaning λ̃_{γ(u)}=λ_u, induces γ'(u,c')=(γ(u),c'). Equations (4) and (7) commute with this map. The outer transport of γ is γ itself, so the mixed comparison is natural. ∎

The theorem is about transport of specified fillers and specified matchings. If outer whiskering makes some u invisible, the target solution groupoid may acquire further fillers or automorphisms. No equivalence of the entire solution groupoids is inferred from this transport law.

## 8 When a diagram of internal retypings commutes

Consider two finite paths of valid internal retypings starting at the same original fully visible square. Suppose their composite maps on B and C are the same functions f_total:B_final→B and g_total:C_final→C. Using (6), let Λ_u and Λ'_u denote the two composite fibre bijections

    g_total^{-1}(c_U(u)) ≅ f_total^{-1}(b_U(u)).

### Proposition 4 Complete comparison of two transport paths

The two transported whole matchings over θ are equal iff Λ_u=Λ'_u for every u. Equivalently, the two transported fillers admit an isomorphism fixing the retyped boundary data, lying over the identity of U, and intertwining their α and β maps iff these equalities hold. Equality of the composite object maps f_total,g_total alone does not suffice.

Proof. If the fibre maps agree, formulas (3) and (4) are identical after the canonical deletion of determined intermediate interface coordinates. Conversely, choose any u and any c' in its final C fibre. Full visibility supplies l∈L_{b_U(u)} and r∈R_{c_U(u)}. The B_final coordinate in the image of that whole witness under (3) is Λ_u(c') on one path and Λ'_u(c') on the other, so equality of whole matchings forces them equal. An isomorphism of fillers preserving α must send (u,c') to itself after the canonical identifications, since α fixes v and c'; its B_final endpoint then forces the same equality. Empty fibres have a unique map and impose no extra condition. ∎

A discrepancy can be presented as the actual nonidentity permutation

    δ_u = Λ'_u Λ_u^{-1}

of f_total^{-1}(b_U(u)). This permutation is derived from the prescribed interface matchings. It is not an extra label attached to the calculus. It obstructs the claimed commuting transport diagram. If a later outer context deletes every whole witness exposing that u, the discrepancy may become unobservable; the equivalence above therefore deliberately uses the original full-visibility hypothesis.

## 9 Exact scope of the transport calculus

For a fixed fully visible original square and fixed inner functions f,g, Theorem 1 gives the maximal class of lifted whole matchings over θ that admit a filler: precisely those constant on each original hidden-witness rectangle. Sections 5, 7 and 8 prove that these compatible internal changes compose, interact coherently with arbitrary outer contexts on specified fillers, and have a complete comparison test for parallel transport paths.

This is a coherent restricted transport calculus with actual witness data. It is not a claim that every internal restriction is valid, that arbitrary multi-square networks are reconstructible, or that all physical interface implementations realize these finite-span maps. Those are distinct obligations.
