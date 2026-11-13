# Reconstruction of a witnessed finite span square

## Plain language summary

Two descriptions can agree on the overall system and on how many internal possibilities exist, yet still disagree about how those possibilities match. This note solves a precise two-sided reconstruction problem: given two factorizations of the same whole and the actual matching between their witnesses, determine whether there is an intermediate component realizing both factorizations at once.

The answer is constructive. The supplied matching makes an incidence diagram between witnesses in the two partial descriptions. A genuine intermediate witness must account for one complete, consistently labelled rectangle in that diagram. When all neighboring interface fibres are nonempty, these rectangles are necessary and sufficient, and they recover the intermediate component uniquely up to a unique structure-preserving isomorphism. A missing rectangle or inconsistent label is a finite obstruction certificate.

Empty interfaces are not discarded. They leave finite tiling choices on one side, or genuinely invisible intermediate witnesses when both sides are empty. The latter retain their actual permutation symmetries. We classify the entire solution groupoid, not only whether a solution exists.

The distinction from support or counting is sharp. With two witnesses on each of four given components, every possible matching has the same support and counts. Nevertheless only four of the twenty-four matchings admit the desired reconstruction. The other twenty fail specifically because of their witness matching.

This is a theorem about one finite-span interpolation square, with a proved outer-context substitution law. It does not by itself establish reconstruction for every crossing network, an arbitrary physical sensor language, or all higher coherence diagrams. No novelty priority claim is asserted here.

## 1 Data and the reconstruction problem

A finite span L:A↝B consists of a finite witness set L and maps a_L:L→A and b_L:L→B. Use the same letter for the span and its witness set where unambiguous. Composition L;U has witnesses (l,u) with b_L(l)=b_U(u). Units are identity spans; composition is associative through the canonical tuple-regrouping bijection.

Fix finite spans

    L:A↝B,   R:C↝D,   V:A↝C,   W:B↝D

and a specified isomorphism of A-to-D spans

    θ:V;R ≅ L;W.

Thus θ is an actual endpoint-preserving bijection

    {(v,r):c_V(v)=c_R(r)} → {(l,w):b_L(l)=b_W(w)}.

It is not merely equality of support relations or equality of cardinalities. The whole witnessed span can be taken to be V;R; θ identifies its other supplied factorization L;W.

A filler is a span U:B↝C and actual isomorphisms

    α:L;U ≅ V,     β:U;R ≅ W

such that, for every composable triple (l,u,r),

    θ(α(l,u),r) = (l,β(u,r)).                       (1)

Equation (1) includes the canonical associator. It asks that the two supplied factorizations be simultaneously realized by the same intermediate witness u. A filler is not allowed to replace the specified θ by a different matching.

A morphism of fillers (U,α,β)→(U',α',β') is an endpoint-preserving bijection γ:U→U' satisfying

    α'(l,γ(u))=α(l,u),   β'(γ(u),r)=β(u,r).          (2)

These objects and morphisms form the solution groupoid Sol(θ). All boundary spans and θ are fixed literally. Permitting isomorphisms of those boundary data would define a different, larger groupoid.

Write

    L_b={l:b_L(l)=b},   R_c={r:c_R(r)=c},
    B_+={b:L_b≠∅}, B_0=B\B_+,
    C_+={c:R_c≠∅}, C_0=C\C_+.

Also write L_ab, R_cd, V_ac and W_bd for endpoint fibres.

## 2 The incidence construction

Form a finite bipartite multigraph Γ_θ. Its left vertices are the individual witnesses v∈V and its right vertices are the individual witnesses w∈W. For every composable pair (v,r), write

    θ(v,r)=(l,w)

and insert an edge from v to w labelled (l,r). Parallel edges are retained. Since θ is bijective, an equivalent construction inserts one edge for every pair (l,w).

Consequently:

- the edges at v are indexed bijectively by all r∈R_c_V(v);
- the edges at w are indexed bijectively by all l∈L_b_W(w);
- a_V(v)=a_L(l), b_W(w)=b_L(l), c_V(v)=c_R(r), d_W(w)=d_R(r) on every edge.

A left vertex is isolated exactly when c_V(v)∈C_0. A right vertex is isolated exactly when b_W(w)∈B_0. No isolated vertex is suppressed.

Call a nonisolated connected component T a labelled rectangle if there are b∈B_+ and c∈C_+ such that:

1. Every right vertex of T has B endpoint b, and every left vertex has C endpoint c.
2. The l label of an edge depends only on its left vertex v. Denote it λ_T(v). The r label depends only on its right vertex w. Denote it ρ_T(w).
3. The maps λ_T:V(T)→L_b and ρ_T:W(T)→R_c are bijections.
4. There is exactly one edge between every left/right vertex pair, with labels (λ_T(v),ρ_T(w)).

The endpoint identities above then say λ_T and ρ_T preserve the remaining A and D types. Some clauses are redundant using θ's bijectivity, but the explicit version makes the certificate directly checkable.

## 3 Reconstruction when both sides are visible

### Theorem 1 Visible rectangle criterion

Assume B_0=C_0=∅. Then Sol(θ) is nonempty if and only if every connected component of Γ_θ is a labelled rectangle. If nonempty, Sol(θ) is contractible: between any two fillers there is exactly one morphism.

A canonical filler has one U witness for each connected component T, with endpoints b,c from condition 1, and

    α(l,T)=λ_T^{-1}(l),   β(T,r)=ρ_T^{-1}(r).       (3)

#### Proof of necessity

Given a filler and u∈U_bc, define

    V_u={α(l,u):l∈L_b},   W_u={β(u,r):r∈R_c}.

Because α and β are bijections, V is partitioned by the nonempty V_u, and W by the nonempty W_u. Equation (1) says that the edges involving these vertices are exactly the pairs

    α(l,u) — β(u,r), labelled (l,r),

for l∈L_b and r∈R_c. Both sides are nonempty, so this is a connected complete bipartite graph. No edge connects different u values. Thus these sets are exactly the connected components, and each satisfies all four rectangle conditions.

#### Proof of sufficiency

Use the components as U and define (3). Each component contributes every L_b witness exactly once on its left and every R_c witness exactly once on its right. Distinct components have disjoint vertex sets and every vertex is nonisolated by hypothesis. Therefore α and β are endpoint-preserving bijections. Condition 4 gives equation (1), so this is a filler.

#### Proof of the groupoid statement

Every filler witness u determines its visible connected component. This gives an endpoint-preserving bijection U→π_0(Γ_θ), and (3) shows that it satisfies (2). It is forced by either nonempty side, hence unique. Every filler therefore has a unique isomorphism to the canonical one. In particular its automorphism group is trivial. ∎

The theorem does not require that the original whole have a unique decomposition or that arbitrary span factorizations have unique lifts. Its uniqueness concerns this fixed, fully witnessed square and the stated nonempty supports.

### Finite obstruction certificates

Failure is witnessed by one of: a component mixing incompatible b or c endpoints; two incident edges giving different l labels at the same v or different r labels at the same w; a failed label bijection; or a missing/repeated rectangle edge. These are properties of the supplied θ, not assertions that a desired global solution fails to exist.

Constructing Γ_θ uses exactly |V;R|=|L;W| edges. Connected components and label-consistency checks are finite. The problem is not reduced to enumerating all candidate U spans.

## 3A A permutation presentation of the obstruction

The rectangle test has a graph-free algebraic presentation. First check the two local conditions:

- in θ(v,r)=(l,w), the value l is independent of the compatible r for fixed nonisolated v;
- in θ^{-1}(l,w)=(v,r), the value r is independent of the compatible l for fixed nonisolated w.

These define λ(v)=l and ρ(w)=r. They also determine the missing b endpoint of v and c endpoint of w. For each fixed b∈B_+,c∈C_+, put

    V_l={v:c_V(v)=c and λ(v)=l}, for l∈L_b,
    W_r={w:b_W(w)=b and ρ(w)=r}, for r∈R_c.

The supplied θ then defines a bijection

    τ_lr:V_l→W_r,    θ(v,r)=(l,τ_lr(v)).

Indeed the inverse is read from θ^{-1}(l,w), and the second local condition forces its r label to be the specified r. Thus all these fibres have a common cardinality n_bc, possibly zero. No additional counting hypothesis is being assumed.

Choose reference witnesses l0∈L_b and r0∈R_c, and set U_bc=V_l0. Define bijections

    a_l=τ_l,r0^{-1} τ_l0,r0 : U_bc→V_l,
    b_r=τ_l0,r : U_bc→W_r,

and permutations

    Ω_lr=b_r^{-1} τ_lr a_l : U_bc→U_bc.             (9)

For l=l0 or r=r0 this permutation is automatically the identity.

### Theorem 1A Holonomy criterion

After the two local conditions pass, a visible filler exists if and only if every Ω_lr is identity, for every b,c. Only (|L_b|−1)(|R_c|−1) permutations need be checked at each pair. If they vanish, the maps a_l and b_r give the filler by α(l,u)=a_l(u), β(u,r)=b_r(u).

Proof. Their coherence equation is exactly τ_lr a_l=b_r, equivalent to (9) being identity. Conversely, suppose any filler maps α_l:U→V_l and β_r:U→W_r exist. They give τ_lr=β_r α_l^{-1}. Substituting into (9) cancels all factors and gives the identity, independently of the identification U≅V_l0. Thus the criterion is necessary as well as sufficient. The constructed filler agrees, through its unique isomorphism, with Theorem 1's component construction. ∎

Changing the names of sheets conjugates the permutations. Changing reference witnesses changes the chosen generating family, but the assertion that every permutation is identity is invariant, as follows either from the theorem or from path transport. In incidence language, the local conditions make Γ_θ a covering of the complete bipartite base with vertices L_b and R_c. A chosen spanning tree identifies its fibres; (9) records transport around its fundamental four-edge cycles. Their number is (|L_b|−1)(|R_c|−1), the rank of the base graph's free fundamental group. A filler exists precisely when this cover is a disjoint union of degree-one copies, equivalently when its permutation holonomy is trivial.

This use of ordinary graph coverings is a presentation of the finite matching obstruction. It is not a hypothesis that the underlying system is a graph, nor a claim to invent graph-covering monodromy.

### A locally consistent matching with nontrivial holonomy

Let L=R={0,1}, V=L×{0,1}, W={0,1}×R, with singleton endpoint types, and set

    θ((l,u),r)=(l,(u XOR (l*r),r)).

This is a bijection. Both local label-independence conditions hold. Every relevant fibre has two elements, so all divisibility tests pass. Choosing l0=r0=0 makes a_l and b_r identity maps, but Ω_11 is the transposition u↦u XOR 1. Thus no filler exists. Its incidence diagram is one eight-cycle rather than two complete two-by-two rectangles.

For general singleton endpoint types and fixed positive l,r with sheet count u, the number of θ satisfying the two local conditions is

    (lu)! (ur)! (u!)^(lr−l−r).

To count them, choose the labelled V_l and W_r fibres, then independently choose the u! bijections τ_lr at each pair. The number of coherent θ is smaller by exactly (u!)^((l−1)(r−1)), yielding (8). Thus the holonomy constraints detect a precisely counted additional failure after local consistency and all cardinalities pass.

## 4 Empty fibres and the full solution groupoid

The visible condition still applies without B_0=C_0=∅. The nonisolated components account exactly for U_bc with b∈B_+, c∈C_+. Empty supports produce three additional sectors.

### Left-only tilings

For each c∈C_0, define a groupoid T^L_c. Its objects are finite sets U_bc for b∈B_+ together with an A-typed bijection

    α_c: coproduct_{b∈B_+} L_b×U_bc ≅ V_c.

Its morphisms are families of bijections of U_bc preserving α_c. Since each L_b is nonempty, every such automorphism is identity. Nevertheless different tilings can give genuinely nonisomorphic objects.

T^L_c is nonempty exactly when there are nonnegative integers n_bc satisfying

    sum_{b∈B_+} |L_ab| n_bc = |V_ac|   for every a∈A.       (4)

Necessity counts α_c by A endpoint. Sufficiency takes U_bc=[n_bc] and chooses a bijection separately in each A fibre. This uses only finite sets. It handles V_c=∅ and empty index sets literally.

For a fixed count vector n, its groupoid is the action groupoid of

    product_a Bij(coproduct_b L_ab×[n_bc], V_ac)

by product_b Sym(n_bc), acting on the copy indices. The action is free because each L_b is nonempty. Thus it is equivalent to a discrete set with cardinality

    product_a |V_ac|! / product_b n_bc! .                    (5)

The formula applies to count vectors satisfying (4). The L witnesses are fixed named witnesses, so there is no additional division by their permutations.

### Right-only tilings

For each b∈B_0, define T^R_b dually. Its objects are U_bc for c∈C_+ and a D-typed bijection

    β_b: coproduct_{c∈C_+} U_bc×R_c ≅ W_b.

It is nonempty precisely when nonnegative n_bc satisfy

    sum_{c∈C_+} n_bc |R_cd| = |W_bd|   for every d∈D.       (6)

It is similarly equivalent to a discrete set of actual typed tilings, with fixed-count cardinality product_d |W_bd|! / product_c n_bc!.

### Doubly invisible witnesses

For each (b,c)∈B_0×C_0, U_bc is wholly invisible to α and β: both L_b×U_bc and U_bc×R_c are empty. It can be any finite set. Its full groupoid is FinSet_iso, equivalent to the disjoint union over n≥0 of the one-object groupoids B Sym(n). These are actual automorphisms of invisible intermediate witnesses, not added decoration.

### Theorem 2 Complete classification

If any nonisolated component fails the rectangle criterion, Sol(θ) is empty. Otherwise there is an equivalence

    Sol(θ) ≃ (product_{c∈C_0} T^L_c)
             × (product_{b∈B_0} T^R_b)
             × (product_{(b,c)∈B_0×C_0} FinSet_iso).       (7)

The visible factor is contractible and has been omitted from the right side. In particular, existence is decided by the rectangle criterion and the finite nonnegative systems (4),(6). Doubly invisible witnesses never obstruct existence, because empty U_bc is allowed, but they prevent a finite cardinality bound on all solutions.

#### Proof

Partition U by the four endpoint-support sectors B_+/B_0 and C_+/C_0. The visible sector is reconstructed as in Theorem 1. In the left-only sector, β imposes no condition and θ has no incident edges; the entire remaining condition is α_c. The right-only sector is dual. In the doubly invisible sector neither isomorphism sees U_bc. These sectors are disjoint, so a filler is exactly their simultaneous choice. The same decomposition applies to its isomorphisms, yielding (7). Conversely, combine the canonical visible filler, chosen tilings and invisible sets; α and β are bijections on disjoint unions and (1) holds on every triple, all of which lies in the visible sector. ∎

The integer systems are finite existential checks rather than a claimed polynomial algorithm. Each n_bc in (4) is bounded by |V_c| because |L_b|≥1; similarly (6) is bounded by |W_b|. Thus simple bounded search already terminates. Only the explicitly classified doubly invisible sector is unbounded.

### Prescribing the abstract middle relation

The theorem is relative to a specified abstract decomposition, not only an unrestricted search for U. Let Ubar⊆B×C be the required support of U. Restrict Sol(θ) to fillers satisfying U_bc≠∅ exactly when (b,c)∈Ubar. Formula (7) remains valid with these explicit restrictions:

- At b∈B_+,c∈C_+, the reconstructed number of rectangle components is forced. Ubar must contain exactly those pairs with a positive number of components.
- In each one-sided tiling, impose n_bc≥1 for pairs in Ubar and n_bc=0 for pairs outside Ubar, in addition to (4) or (6).
- At b∈B_0,c∈C_0, use the groupoid of nonempty finite sets if (b,c)∈Ubar, and the terminal groupoid of the empty set otherwise.

These are necessary and sufficient and classify the entire relative solution groupoid. Support-level solvability therefore does not suffice: even when Ubar composes to the given parent supports, the labelled rectangle test or integer tiling constraints can fail.

## 5 Witness coherence is strictly stronger than support or counts

Take all four object sets A,B,C,D to be singletons. A finite span is then just a finite witness set. Let

    |L|=l, |R|=r, |V|=lu, |W|=ur,

where l,r>0 and u≥0. Both whole factorizations have lur witnesses. Every bijection θ:V×R→L×W has the same support and multiplicity data, and the cardinality equations for U are solved by |U|=u.

### Theorem 3 Exact count of coherent matchings

The number of θ admitting a filler is

    (lu)! (ur)! / u! .                                  (8)

The total number of θ is (lur)!.

Proof. Fix U=[u]. There are (lu)! choices of α and (ur)! choices of β. Every pair determines θ through (1). Relabelling U by Sym(u) leaves θ unchanged. This action on pairs is free because l,r>0. By Theorem 1, two pairs induce the same θ exactly when their fillers are uniquely isomorphic, hence differ by such a relabelling. Thus the orbits are exactly the coherent θ, proving (8). The u=0 case is one empty matching, with 0!=1. ∎

For l=r=2,u=1, four of the twenty-four θ lift. Identify V,R,L,W with {0,1}. The bijection

    θ(v,r)=(v XOR r,r)

does not lift: its l label varies with r at the same v. All support and count conditions pass. This is a precise witness-matching obstruction.

There is also a separate count obstruction: l=r=2 and |V|=|W|=1 gives equal whole counts 2=2, but any U would require 2|U|=1. Support exactness alone does not even imply an integer-sized filler.

If θ is only partially observed, let Θ be a specified collection of allowed endpoint-preserving bijections, retaining each actual θ as a distinct possible matching. The total solution groupoid is the disjoint union of Sol(θ) over θ∈Θ. In the fully visible case it is equivalent to the discrete set of allowed coherent θ. This gives genuine nonunique realizations when several matchings satisfy the observation. It does not silently identify them or introduce symmetries not present in the boundary data.

## 6 Outer-context substitution and interface restriction

Let H:A'↝A and K:D↝D' be arbitrary finite spans. Whisker the square to obtain

    H;V;R;K ≅ H;L;W;K,

or, regrouped, a square with boundaries

    L'=H;L, R'=R;K, V'=H;V, W'=W;K.

The new θ' sends a matching tuple (h,v,r,k) to (h,l,w,k) whenever θ(v,r)=(l,w).

### Theorem 4 Coherent transport of existing fillers

Every filler (U,α,β) of θ induces a filler of θ' with the same U and

    α'(h,l,u)=(h,α(l,u)),
    β'(u,r,k)=(β(u,r),k).

This gives a functor Sol(θ)→Sol(θ'). Successive outer substitutions and identity contexts agree through the canonical tuple-associator and unit isomorphisms. These comparisons satisfy their coherence equations because both routes act identically on fully written tuples.

Proof. Composition of a span isomorphism with a fixed span remains an isomorphism. The displayed formulas are endpoint-preserving bijections and the equality θ'(α'(h,l,u),r,k)=(h,l,β'(u,r,k)) is (1) with unchanged h,k. Equations (2) are likewise preserved. Repeated substitutions merely add the corresponding context coordinates, so the coherence assertion follows literally on tuples. ∎

This is a genuine horizontal-composition statement, not only precomposition of an output function. It does not claim that the functor is an equivalence: a context can remove visible witnesses and make previously impossible or distinguishable fillers possible or indistinguishable.

As a special case, pull back outer A and D interfaces along functions f:A'→A and g:D'→D. The graph/converse-graph spans implement these restrictions. Existing fillers transport. If f and g are surjective, filler existence is also reflected: choose set-theoretic sections and restrict back to the original square. This existence statement does not claim that all new fillers or morphisms descend, especially in the one-sided empty sectors.

An obstruction can disappear under a nonsurjective restriction. For example, discard every A value supporting an obstructing component and the restricted square may become empty. This is why a witness obstruction is relative to a specified square and context, not an invariant under all forgetful operations.

## 6A Internal retyping is not independent Cartesian transport

Let f:B'→B and g:C'→C. Pull back L,W at B', and V,R at C', giving L',W',V',R'. The naive candidate middle is

    U'=B'×_B U×_C C'.

There are canonical endpoint-preserving maps, not automatically isomorphisms,

    κ_α:L';U'→V',    ((l,b'),(b',u,c'))↦(α(l,u),c'),
    κ_β:U';R'→W',    ((b',u,c'),(c',r))↦(b',β(u,r)).

For each (v,c')∈V', write α^{-1}(v)=(l,u). The fibre of κ_α over (v,c') is exactly f^{-1}(b_U(u)). Dually, for each (b',w)∈W', writing β^{-1}(w)=(u,r), the fibre of κ_β is exactly g^{-1}(c_U(u)). Consequently both comparison maps are isomorphisms precisely when these specific fibres are singletons for every target witness. Empty target sets impose no condition.

When both comparisons are isomorphisms, they induce a coherent θ' over θ and give the naively transported filler. In general independently retyping the four sides need not even supply a specified isomorphism V';R'≅L';W'; such an isomorphism requires new matching data. This is not the outer restriction theorem of Section 6.

For example start with singleton object sets and singleton spans, and let both B' and C' have two elements mapping to their singleton originals. Then U' has four witnesses; each of L';U' and U';R' has four witnesses, while V' and W' have two. The canonical comparisons are not isomorphisms. Nevertheless a chosen bijection t:B'→C' gives a different middle span with witnesses {(b',t(b'))}, which does fill a suitable newly chosen θ'. The two bijections give different matching choices when B',C' are fixed. Independent Cartesian pullback includes all four pairs rather than choosing the coherent alignment. The alternative two-witness filler has diagonal support, not the full pulled-back abstract support B'×C'. If that full support is prescribed, no such alternative is a relative lift: four required support pairs already demand at least four middle witnesses, while the parent isomorphisms force two.

Thus the theorem proves horizontal outer-context transport and a sharp test for naive internal retyping; it does not silently promote the latter to a universal equipment exactness law.

## 7 Relation to the larger reconstruction problem

The equation θ(α(l,u),r)=(l,β(u,r)) is a two-sided compatibility requirement between supplied factorizations. The incidence criterion computes whether an actual intermediate witness structure exists and classifies all of it. It does not infer a filler merely from the equality V;R≈L;W, nor from equality of supports or matrices of cardinalities.

The ambient structure is the bicategory/equipment of finite spans, with actual witness maps and its canonical composition/restriction operations. The theorem uses pullback composition essentially to derive the rectangle condition and prove contextual substitution. The diagnostic incidence diagram is an algorithmic representation of witness data, not an assumption that the systems themselves are graphs.

This square is a precise local interpolation problem. Extending it to a whole family of crossing cuts requires additional compatibility between reconstructed squares. Contractibility of a visible fixed-square fibre does not alone establish that global higher compatibility. Physical admissibility restrictions may also exclude the reconstructed U or its maps; those must be checked in the chosen implementation category rather than assumed from the span semantics.

The mathematical proofs have independent nonauthor AI review, including the empty-fibre and prescribed-support cases; this is not human certification or Lean verification. An author checker compared the rectangle test against explicit filler constructions for 43,306 matchings across 64 specified singleton-endpoint profiles. Independently written checks also tested the two-by-two permutation counts and finite typed empty-fibre cases. These are bounded checks, not exhaustive validation of arbitrary finite spans. Standard ingredients include finite spans, bipartite incidence, bijection counting, and groupoid decompositions. The specific classification and its use as a witnessed interpolation obstruction should be compared with existing span factorization/descent results before making any claim of originality.
