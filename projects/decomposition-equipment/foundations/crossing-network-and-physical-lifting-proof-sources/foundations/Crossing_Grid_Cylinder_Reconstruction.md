# Reconstruction for a genuine crossing four component grid

## Plain language summary

An intermediate span solving a two-sided factorization problem is not automatically a common refinement of two crossing decompositions. In a four-component system, one component can be grouped with a parallel component in one decomposition and with its serial neighbor in another. Reconstructing the missing component must leave that parallel component genuinely unchanged, not merely preserve the overall input/output behavior.

This note adds that missing condition. First reconstruct the fully witnessed interpolation square. Then test whether its intermediate component is the same component at every value of the parallel interface, and whether the original parallel witnesses pass through unchanged. These requirements can be checked directly from the reconstructed witness matchings. They give a necessary and sufficient criterion, not an assumption that the common refinement already exists.

The result is for finite spans with explicitly nonempty visible fibres. It retains actual witness isomorphisms. It is not a theorem for every physical implementation language or every higher crossing network.

## 1 Four components and two crossing groupings

Fix finite spans

    R:A↝B,   Q:K↝L,   S:C×L↝D,

and given parent spans

    P:A↝C,   N:B×L↝D.

The missing fourth component is T:B↝C. The intended whole has components R,T,Q,S: R feeds T, while T and Q jointly feed S. The first grouping is

    {R,T} | {Q,S},

and the second grouping is

    {R,Q} | {T,S}.

These partitions of the four component occurrences cross: their four intersections are R,T,Q,S. There is no claim that merely inserting an identity component into a serial chain would establish this distinction. Q and S may have nontrivial witnesses and behavior.

The first grouping has the known macro P for R;T and the known macro (id_C×Q);S for {Q,S}. The second grouping has the known macro R×Q and the given macro N for {T,S}. Supply an actual whole-witness isomorphism

    θ:(P×Q);S ≅ (R×Q);N.                              (1)

Canonical product/composition rearrangements identify the left side with the whole obtained from the first grouping. θ is part of the input, not merely equality of endpoint supports.

A crossing-grid realization consists of T and isomorphisms

    α0:R;T ≅ P,
    β:(T×id_L);S ≅ N,                                (2)

such that

    θ((α0(r,t),q),s) = ((r,q),β((t,l),s))             (3)

whenever q has output l and s has input (c_T(t),l). This preserves Q as the same component occurrence with the same actual witness q.

Isomorphisms between realizations are span isomorphisms of T commuting with both maps (2). All given boundary spans and θ are fixed.

## 2 Visibility assumptions

Assume L is nonempty, and assume each of the following fibres is nonempty:

    R_b={r:output(r)=b}, for every b∈B;
    Q_l={q:output(q)=l}, for every l∈L;
    S_(c,l)={s:input(s)=(c,l)}, for every (c,l)∈C×L.  (4)

No assumption requires every A or K input fibre to be populated. Conditions (4) concern exactly the witnesses that make the unknown middle component visible from both sides. They imply that the interpolation square below satisfies the fully visible hypotheses of Witnessed_Square_Reconstruction.md, Theorem 1.

Set

    L0=R×Q, R0=S, V0=P×Q, W0=N.

The interpolation problem asks for an arbitrary U:B×L↝C×L with isomorphisms L0;U≅V0 and U;R0≅W0 coherent with θ. A crossing-grid realization is stronger: it requires U to be cylindrical, namely T×id_L, and its first isomorphism to be exactly α0×id_Q under tuple reassociation.

## 3 Explicit cylinder criterion

Apply the labelled-rectangle test, equivalently the local-label and permutation-holonomy tests, of Witnessed_Square_Reconstruction.md to (L0,R0,V0,W0,θ). If it passes, let

    (U_can, α_can, β_can)

be the canonical component filler. Every other square filler has a unique isomorphism to this one.

The following three additional tests are entirely explicit.

### Test Q Actual parallel witnesses are preserved

For every input witness ((p,q),s), if

    θ((p,q),s)=((r,q'),n),

require q'=q literally. Equal endpoint values of q and q' are insufficient.

Under this test every U_can witness has endpoints (b,l) and (c,l) with the same l. Indeed choose an incoming (r,q), apply α_can, and then choose an outgoing s, which is possible by (4). Coherence with θ and preservation of q forces the q in the output of α_can to equal the chosen input q, hence their L endpoints agree. Write U_l for the resulting B-to-C span of U_can witnesses at level l.

The same argument proves

    α_can((r,q),u)=(p,q) for u∈U_l and q∈Q_l.

For fixed q∈Q_l this defines an isomorphism R;U_l≅P.

### Test F The same intermediate witness means the same factor at each parallel witness

For u∈U_l with B,C endpoints b,c and q∈Q_l, define its descriptor

    d_(u,q)=(b,c, φ_(u,q)),
    φ_(u,q):R_b→P_c,
    α_can((r,q),u)=(φ_(u,q)(r),q).                  (5)

Here P_c is the set of P witnesses ending at c; the function preserves A endpoints. Require d_(u,q) to be independent of q for each fixed u,l. Denote the resulting descriptor d_u.

This is stronger than saying that the unlabelled sets of tilings induced by two q values agree. A q-dependent permutation of the U_l witnesses may leave those sets equal while changing the actual factor used by β_can. Such a permutation fails this test.

### Test L The same component is used at every parallel output value

For each l define the finite set of actual descriptors

    T_l={d_u:u∈U_l}.

Require T_l=T_l' literally for every l,l'∈L. The descriptors include the B,C endpoints and the full maps (5), so this is not merely equality of cardinality or support.

For fixed l the map u↦d_u is injective. If u,u' had the same descriptor, choose r∈R_b using (4), then α_can would send distinct composable pairs to the same (p,q). It is therefore a bijection U_l→T_l.

## 4 Reconstruction theorem

### Theorem Crossing grid reconstruction

Under (4) and L≠∅, the crossing-grid realization groupoid is nonempty if and only if:

1. the fully witnessed interpolation square passes its rectangle/holonomy criterion;
2. Test Q holds;
3. Test F holds for its canonical filler;
4. Test L holds.

If nonempty, the realization groupoid is contractible. Its canonical middle component T is the common finite descriptor set T_l, with the B,C endpoints included in each descriptor. The theorem also solves the problem relative to a prescribed abstract middle relation Tbar⊆B×C: require in addition that this canonical T have support exactly Tbar.

#### Proof of necessity

Given T,α0,β as in (2),(3), set U=T×id_L. This is a square filler. Theorem 1 of the companion note supplies its unique isomorphism to U_can. Equation (3) gives Test Q. Under that isomorphism, a witness (t,l) has descriptor (b_T(t),c_T(t),r↦α0(r,t)), independently of q, proving Test F. The same descriptors occur at every l, proving Test L. The map t↦its descriptor is injective because R_b is nonempty and α0 is injective; it is surjective onto T_l by construction. Thus the canonical descriptor set recovers T up to the required unique isomorphism.

#### Proof of sufficiency

Let T be the common descriptor set. Define

    α0(r,t)=φ_t(r).

Choose any l∈L and any q∈Q_l. The map α_can at that fixed q is a bijection R;U_l→P, and u↦d_u is a bijection U_l→T. Thus α0 is an endpoint-preserving bijection R;T→P. Its definition does not depend on the chosen l or q.

Let γ_l:T→U_l be the inverse descriptor bijection. Together these form an isomorphism γ:T×id_L→U_can. Tests F and L give

    α_can((r,q),γ_l(t))=(α0(r,t),q).

Define β((t,l),s)=β_can(γ_l(t),s). This is an isomorphism (T×id_L);S→N. Coherence of the canonical square filler now gives (3). Thus T,α0,β is a crossing-grid realization.

#### Proof of the groupoid statement

The necessity proof assigns every realization a bijection from its T to the canonical descriptor span. Compatibility with α0 forces this bijection, because each R_b is nonempty. Compatibility with β follows from the unique square-filler comparison and equation (3). Hence every realization has a unique isomorphism to the canonical one, and there are no nontrivial automorphisms in this fully visible, fixed-data fibre. ∎

## 5 Outer-context coherence

Let H:A'↝A and J:D↝D' be arbitrary finite spans. Replace R,P by H;R,H;P and replace S,N by S;J,N;J; keep Q fixed. Whisker θ by H×id_K on the source and J on the target.

Every existing crossing-grid realization transports with the same T, using

    α0'(h,r,t)=(h,α0(r,t)),
    β'((t,l),s,j)=(β((t,l),s),j).

These are isomorphisms and preserve the unchanged Q witness. Their coherence equation is (3) with h and j carried unchanged. Successive context substitutions and identity contexts agree through canonical tuple associators, satisfying the coherence laws literally on fully written tuples.

The new context may destroy the visibility assumptions. The transport of an existing realization remains valid, but the contractibility and explicit complete classification theorem above then need not apply. This is not a claim that context substitution induces an equivalence on all realization groupoids.

Internal changes of B,C,L or changes to Q require their own witness comparisons. Independent Cartesian restriction of the square is not automatically a cylindrical transport, as the companion internal-retyping analysis demonstrates.

## 6 Internal interface changes and their exact lifting condition

Start with a realized visible grid T,α0,β and θ as above. Let f:B'→B and g:C'→C. Keep Q and L fixed, and form the prescribed retyped parent spans

    R_f:A↝B',   P_g:A↝C',
    S_g:C'×L↝D,   N_f:B'×L↝D

by Cartesian endpoint restriction. For example R_f witnesses are (r,b') with f(b')=b_R(r). These data do not automatically give a whole matching. Suppose an actual matching

    θ':(P_g×Q);S_g ≅ (R_f×Q);N_f

is supplied and commutes with the maps forgetting b',c' to θ.

For each old composable whole tuple (r,t,q,s), with q ending at l and s starting at (c_T(t),l), this θ' is exactly a bijection of the retyping fibres

    η_(r,t,q,s):g^{-1}(c_T(t))→f^{-1}(b_T(t)).       (6)

Its defining equation is

    θ'(((α0(r,t),c'),q),(c',l,s))
      = (((r,b'),q),(b',l,β((t,l),s))),
    where b'=η_(r,t,q,s)(c').

The assertion follows because forgetting retyping witnesses fixes the old whole tuple, and θ' is a bijection over θ. In particular the fibre cardinalities must match for each t that occurs. Full visibility ensures every t occurs. If both fibres are empty there is their unique empty bijection; unequal cardinalities prevent even such a θ'.

### Theorem Internal retyping of a crossing realization

There is a crossing-grid realization of the retyped data θ' if and only if the bijections (6) depend only on t. Equivalently there are bijections

    λ_t:g^{-1}(c_T(t))→f^{-1}(b_T(t))

such that η_(r,t,q,s)=λ_t for every composable tuple. In particular the choice must be independent of the parallel output l, not merely independent of r and s at a fixed l.

When the criterion holds, a canonical new middle span has witnesses

    T'={(t,c'):g(c')=c_T(t)},

with endpoints (λ_t(c'),c'). Its two parent maps are

    α0'((r,b'),(t,c'))=(α0(r,t),c'),
    β'(((t,c'),l),(c',l,s))=(λ_t(c'),l,β((t,l),s)),

where the first formula is used when b'=λ_t(c'). These are actual isomorphisms and give the supplied θ'.

#### Proof

Sufficiency follows directly from the displayed formulas. For α0', the inverse of a target (p,c') first uses α0^{-1}(p)=(r,t), then takes b'=λ_t(c'). For β', first use β^{-1}(n)=((t,l),s), then recover c'=λ_t^{-1}(b'). Thus both maps are bijections. Their coherence is exactly η=λ.

For necessity, let T'',α0'',β'' be any retyped realization. Fix a T'' witness z with endpoints b',c'. For each r∈R_f(b'), α0''((r,b'),z)=(p,c'). Use any compatible q and s, which exist by visibility. Projecting the coherence equation to θ forces α0^{-1}(p)=(r,t) for some old t and forces the projection of β''((z,l),(c',l,s)) to equal β((t,l),s). At fixed z,l,s the latter expression is independent of r. Injectivity of β therefore makes t independent of r. The equation involving α0'' also makes t independent of q,s,l. Hence z determines a unique old t, with the corresponding B,C endpoints.

For each pair (t,c'), choose any r∈R_b. The bijectivity of α0'' on the target (α0(r,t),c') supplies exactly one z over (t,c'), across all possible b'. Independence from r makes this assignment well-defined. It defines a function λ_t(c')=b'. The bijectivity of β'' makes λ_t a bijection onto f^{-1}(b_t), by the dual argument using an available s. Finally coherence with the specified θ' forces every η_(r,t,q,s) to equal this λ_t. This proves necessity. ∎

This is a classification of coherent internal interface lifts, not independent Cartesian pullback of the middle. The support of T' is the union of the graphs of the λ_t. It need not be the full pullback B'×_B supp(T)×_C C'. If a new abstract middle support is prescribed, compare it with this actual support; a full-pullback support requirement can make the relative lifting problem impossible.

For example, with two parallel L values, a single original t, and two-element retyping fibres, choose λ at the first L value to be identity and at the second to be the transposition. This supplies an ordinary square alignment at each level, but no cylindrical middle T' can use both: the required η depends on l. A constant choice at both levels does lift.

### Composition and mixed coherence of successful internal lifts

Suppose a second internal change is f':B''→B', g':C''→C', with successful fibre bijections λ'_(t,c') for the first lifted middle witnesses (t,c'). The composite lift for f∘f', g∘g' uses

    λ''_t(c'')=λ'_(t,g'(c''))(c'').

This is a bijection: the domain is the disjoint union of the g' fibres over c'∈g^{-1}(c_t), the first λ_t bijects those indexing values with b'∈f^{-1}(b_t), and each λ' bijects the corresponding fibres. The iterated middle witnesses ((t,c'),c'') identify canonically with (t,c''). Under that identification the iterated α0 and β maps equal the maps for λ''. Three successive changes give the same nested evaluation, so the associativity and identity coherence equations hold.

Successful internal lifts also commute with the outer span contexts of Section 5 through canonical tuple regrouping. Both orders use the same middle witnesses (t,c'), the same λ_t, and the maps obtained by carrying h and j unchanged through α0' and β'. Thus both orders give identical formulas on the fully written witnesses (h,r,t,c',q,s,j). This is a proved forward transport law. If a context destroys visibility, it does not imply the converse classification or equivalence of whole realization groupoids in that context.

## 7 Scope and what is not assumed

The theorem does not assume that the four component intersections can be realized, that a cylindrical middle exists, or that the square's filler respects Q. It derives these conditions from the given witnesses and tests them. The fixed-span comparison is a preliminary step; Tests Q, F and L supply the additional genuinely crossing factorization requirements.

The theorem handles this four-corner schema, not every network topology or arbitrary family of crossing cuts. If supplied overlap matchings themselves vary, the global realization problem needs additional compatibility conditions. If an implementation language permits only certain middle components or maps, the reconstructed T,α0,β must also belong to that language. Finite-span existence does not silently grant physical sensors or operations.

Full visibility is essential to the simple contractible-fibre statement. Empty fibres can leave tilings, missing comparison data or invisible witnesses. The companion square theorem classifies those sectors for an arbitrary middle U. The separate note Crossing_Grid_All_Fibres_Classification.md supplies a bounded-matching and invisible-fibre classification for the actual grid; it is not the same efficient visible descriptor criterion proved here.

The mathematical proof has independent nonauthor AI review, including the internal retyping and mixed coherence statements; this is not human certification or Lean verification. Author and independently written checks each compared the visible cylinder criterion with explicit realizations for 332,952 specified finite matchings. Additional bounded checks distinguish ordinary square alignments from genuine cylindrical interface lifts. These finite checks do not replace the general proofs. The ingredients include standard finite-span composition and ordinary bijection/covering theory. No claim that these ingredients are new is made.
