# F4: actual edge-forgetting map, all-degree lifting and its limits

Author mathematical proof, 31 October 2026. Submission, not whole-program acceptance.
Target: original contract v0.1 F4 (M), unchanged contract SHA-256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.

## 0. Dependencies and exact scope

The primary object is the original ordered graph-cut simplicial **set**, recovered in CUT §4, not the ordinary nerve of refinement. C1 §§1–3 supplies its actual small category K, arbitrary ordered partitions (blocks need not be contiguous), actual arrows, and increasing-enumeration identities R1–R3. CUT §§1–4 supplies all-degree simplicial laws, unital 2-Segality and its explicit embedding in the span-coefficient cut groupoid. We reuse these results, not reprove their substantial construction. Graph sizes may be bounded by any N, or unbounded; K may be any small category (finite K gives the original finite subfamily). No thinness, unique factorization, or cancellation of K is assumed. The direct discrete formulas and proof in §§1–3 permit any small K; the faithful embedding into finite-span records asserted by CUT §4 is invoked only for the original finite K with its faithful tagged finite-set functor F, not for arbitrary small K.

Sources:
- CONTRACT: `/workspace/shared/contract_revision_20261028/final_artifacts/Original_Completion_Contract_v0.1_VERBATIM.md`, F4.
- C1: `/workspace/shared/contract_revision_20261028/extracted/witnessed_decompositions/research/workstream_C1/proof/C1_Model_Theorem.md`.
- CUT: `/workspace/shared/contract_revision_20261028/structural_extracted/proof/Global_Cut_Repair.md`.

F4's designated operation forgets **graph edges only**. For general K it retains the actual K-arrow string, not merely its endpoints. In the original finite three-object chain this distinction is invisible because an arrow is determined by its endpoints. In the full CUT extension it retains all span and comparison-bijection data. Forgetting those as well is a different map, not proved CULF here.

## 1. Explicit primary source, target and map

An n-simplex of X is `(G,(U_1,...,U_n),(h_1,...,h_n))`, where G is a simple ordered graph on [v], U is an ordered partition of [v] allowing empty blocks, and `h_i:A_(i-1)→A_i` are actual composable K-arrows. Each interval graph is the induced graph on the union of its blocks, canonically relabelled in increasing order; each interval arrow is the corresponding composite. Thus X_1 is the set of actual whole components `(G,h)` and X_0 is Ob(K): a zero-block partition forces v=0, and the empty composite is id_A. These are precisely the original flat-cut witnesses: output `(G,h_n...h_1)`, inputs `(G|U_i,h_i)`, and retained partition U (C1 §1; CUT §4).

Y_n consists of `([v],(U_1,...,U_n),(h_1,...,h_n))` with exactly the same conditions except no adjacency relation. Define `F_n:X_n→Y_n` by deleting E(G), retaining every other field. The target is exactly the edge-erasure image construction; equivalently it is the edgeless-graph subobject with the known constant adjacency field suppressed.

For any monotone `α:[m]→[n]`, let `V=⋃_(α(0)<r≤α(m)) U_r`. Both X(α) and Y(α) restrict to the increasingly enumerated V; their j-th block is the inverse image of `⋃_(α(j-1)<r≤α(j)) U_r`. Their j-th arrow is `h_(α(j))...h_(α(j-1)+1)`, the identity if that interval is empty. X(α) additionally takes G|V. This is CUT (2.1) restricted to the original slice. R1–R3 and category associativity prove the supplied simplicial laws. Since discarding adjacency commutes with restriction, `F_m X(α)=Y(α) F_n`: F is an actual all-degree simplicial map. In particular outer faces are defined, not omitted.

## 2. All-active cartesian theorem (sets)

A monotone map α is active when `α(0)=0` and `α(m)=n`. For every such α, the square

```
             X_n  --F_n-->  Y_n
              |             |
           X(α)           Y(α)
              |             |
             X_m  --F_m-->  Y_m
```

is a pullback of sets. Equivalently the comparison

`c_α:X_n → X_m ×_(Y_m) Y_n`, `x ↦ (X(α)x,F_n x)`

is bijective in every degree.

**Proof by explicit inverse.** A pullback element is a coarse source simplex a and fine target simplex b satisfying `F_m(a)=Y(α)(b)`. Activity means the selected subset V in b is its entire ordered vertex set, including when some or every block is empty. Consequently b has exactly the same ambient [v] as the whole graph G_a of a. Put

`L_α(a,b)=(G_a, blocks(b), arrow_string(b))`.

This is a valid X_n simplex: the fine partition covers precisely that [v], and the fine arrow string is composable. Its image under F is b. Under X(α), its graph remains G_a, its blocks and arrows are exactly those of a by the pullback equality. Therefore X(α)L=a. Conversely any lift must have b's full partition and arrow string, and because α retains the entire graph, it must have exactly G_a's adjacency. There are no other fields to choose. Hence the lift is literally unique; both inverse identities follow by field equality. This proof includes n=0, m=0, constant active maps to [0], empty graphs, repeated blocks, noncontiguous blocks, parallel K-arrows and nontrivial composites. □

This is not a hypothesis equivalent to CULF in disguise: the assumptions are the concrete independently supplied graph/partition carriers and the restriction formulas. The inverse is derived explicitly from them. Unique factorization of K is neither assumed nor concluded: the fine arrow factorization is already part of b.

## 3. Conservativity and CULF, separately exhibited

In the standard convention CULF means cartesian on active maps; equivalently conservative (cartesian on degeneracies) and unique lifting of factorisations (cartesian on inner faces and their composites). Every codegeneracy `σ^i:[n+1]→[n]` is active, so §2 proves the naturality square of each degeneracy `s_i:X_n→X_(n+1)` is cartesian. Explicitly, if F(z)=s_i(y), the inserted block of z is empty and its inserted arrow is an actual identity, because F retains both these fields. Deleting this slot gives the unique x with z=s_i(x), F(x)=y. The graph is unchanged. This includes endpoint insertions and identity-grade empty wholes. It does **not** declare every empty-graph loop to be a unit.

Every inner coface is active, so §2 gives its unique factorisation lift. More strongly it already treats every active map directly, without relying on an unchecked generating-set assertion. Thus F is CULF in all degrees. Nothing is claimed about general outer-face squares: these discard vertices and edges, and need not have unique lifts.

## 4. Whole and witness nonidentifiability

For the noninjectivity assertion assume K has at least one object and, if a graph-size bound is imposed, N≥2 (the original N≥6 family satisfies this). Fix any K-arrow h, even an identity, and [2]={0,1}. Let G_0 have no edges and G_1 have the single edge {0,1}. Then `(G_0,h)≠(G_1,h)` in X_1, but their F_1 images are equal. Thus F is not injective on whole components and cannot recover the whole from its image.

More generally, over any fixed ordered [v] and actual K-arrow h, the fibre of F_1 has exactly `2^(v(v−1)/2)` elements: the unordered pairs of distinct vertices may independently be chosen as edges. This holds for every permitted v, including v=0,1 where the fibre is a singleton. Thus large whole fibres coexist with singleton active-lifting fibres once the source whole is fixed; this is not merely a two-point regression.

For any composable path h_1,h_2 with composite h, give these two graphs the same partition `({0},{1})`. Both fine cuts have the same F_2 image; indeed their isolated input components are the same, since both singleton induced graphs are edgeless. Their retained whole and total witness differ. For each of the two *separately fixed* source wholes the prescribed target cut has exactly one lift by §2. These are not two lifts of one fixed whole: they have different a-coordinates in the pullback. This is precisely why CULF does not imply recovery or observational identifiability.

The six-vertex mixed-interface case may instead use the original C1 graph and its added cross-edge {0,5}, preserving its specified four blocks and `0→1→1→1→2` path. Both map to the same Y-simplex while their wholes differ. C3 supplies the wider cross-edge information-loss analysis; the concrete pair above independently establishes F4's required X evidence.

## 5. Full CUT groupoid extension: homotopy, not set uniqueness

Let 𝓧 be exactly CUT §§1–3: objects retain G, U, fixed interface sets A_i, interval spans S_ij, and actual coherent comparison bijections ψ_ijk; morphisms fix G,U,A_i and consist of endpoint-preserving span isomorphisms satisfying CUT (1.2). Let 𝓨 be the same interval-record construction with G replaced by its ordered vertex set [v], retaining U,A,S,ψ and all morphisms. Let 𝓕 discard edges only. Both are simplicial groupoids under CUT (2.1), and 𝓕 is simplicial by the same restriction calculation. 𝓨 is the edgeless restriction of CUT, so its all-degree unital 2-Segality is also inherited from the existing proof; no arbitrary nonexact quotient cells are inserted.

For active α, the comparison from 𝓧_n to the **homotopy** pullback `𝓧_m ×^h_(𝓨_m) 𝓨_n` is an equivalence. An object of that pullback is `(a,b,θ)` with `θ:𝓕(a)≅𝓨(α)b`. Morphisms of 𝓨 fix vertex set, blocks and interfaces, so θ guarantees literal equality of those coarse fields. Form x using a's whole graph and b's full fine partition, interfaces, spans and ψ. Activity retains a's entire graph. Then 𝓕(x)=b and θ lifts to an isomorphism `a≅𝓧(α)x`: its span components are unchanged, and both sides now have the identical graph and partition. This gives essential surjectivity of the comparison.

For full faithfulness, a morphism between comparison images is a pair `(u,v)` with `𝓕(u)=𝓨(α)(v)`. The morphism v specifies the entire family of fine span isomorphisms. The morphism u forces equality of the original whole graphs, while v forces equality of fine partitions and interfaces. Thus the same fine span family defines a unique morphism in 𝓧_n; it maps to v, and its α-restriction equals u because the latter equality holds on every coefficient field and graph/partition fields have no extra morphism data. Conversely every source morphism gives such a pair. Hence the comparison is fully faithful and therefore an equivalence. All degeneracies are included.

The strict pullback square is also a pullback with literal field equality, but that alone would not prove the homotopy statement; the preceding argument treats arbitrary θ. “Unique lift” in this groupoid doctrine means a contractible groupoid of lifts of specified homotopy-pullback data, not uniqueness of an arbitrarily chosen span representative. CUT §4's faithful tagged graph-span slice recovers exactly the literal set theorem §§1–3; it is not an identification of all span records with discrete original witnesses.

## 6. Deliberate duplicated-cut-witness control

Here is a lawful all-degree simplicial witness extension on the **same cuts**, rather than a bare two-point-to-point map. Use the actual scalar extension permitted by the ambient CUT equipment with M=C₂, written additively. Define D_n by adjoining to each original X_n record a bit a_ijk for each `0≤i≤j≤k≤n`. Require a_iik=a_ikk=0 (canonical units) and, for every i≤j≤k≤l,

`a_ijk+a_ikl = a_jkl+a_ijl` in C₂.

The scalar tags are discrete retained data: equality compares every bit, and no gauge equivalence identifies different tags. In the full groupoid version morphisms also fix all scalar tags, so labels 0 and 1 remain nonisomorphic. The additive identity 0 here is exactly the multiplicative scalar identity 1 used in CUT.

This is exactly the scalar associativity equation on interval triangles: the two ways to compose their supplied scalar-labelled witnesses agree. Faces and degeneracies restrict the indices by α. Repeated-index normalization and every four-index equation are inherited under every weakly monotone α; index restriction composes literally. Thus D is an actual all-degree simplicial set, and P:D→X forgetting these scalar witness labels is simplicial. The same construction works on full CUT coefficient records with morphisms retaining the scalar labels.

In degree 1 there are no nonrepeated triangle labels, so D_1=X_1. In degree 2 there is exactly one free label a_012∈C₂, and no four-distinct-index constraint; all constraints with repeated indices reduce to identities. Consequently, for **the same fixed whole**, **the same two input components**, **the same partition**, and **the same K-arrow path**, there are two distinct binary cut witnesses, labelled 0 and 1. Both have the same long edge and the same P_2 image. The active long-edge map `[1]→[2]`, `0↦0,1↦2`, therefore has a two-element fibre in its lifting comparison. P is not ULF and not CULF. Composing P with edge-erasure F also fails at the same square. This control directly separates erased witness multiplicity from erased whole edges.

No 2-Segality claim is made for D: indeed over a fixed degree-3 X-record its four triangle bits satisfy one independent equation and give 8 possibilities, whereas either triangulation sees only two arbitrary triangle bits and hence 4 possibilities. Its scalar factor therefore fails that 2-Segal comparison. F4 requires a separate map failing lifting, not a new positive recognition theorem. This control is a coherent scalar-decorated **witness model** and a fully defined simplicial map, not an ad hoc duplicated degree-2 set with missing higher simplicial identities. It is not used to discharge F3 or I3.

### 6.1 Supplementary failure even with a 2-Segal source

To separate the preceding witness duplication from failure of 2-Segality, define `B_n=X_n×(C₂)^n`, where the n bits label the n arrows of the nerve of the one-object group C₂. Inner faces add adjacent bits, outer faces delete the first or last bit, and degeneracies insert 0. More generally an α interval replaces its bits by their sum on that interval. These formulas satisfy every simplicial identity by associativity and the zero identity; B is the product of the actual X with that ordinary nerve. The nerve is Segal, hence unital 2-Segal, and all the triangulation/unit comparisons of B are products of those for its two factors, hence bijective. The projection `Q:B→X` is therefore a simplicial map between unital 2-Segal objects.

Fix a whole `(G,h,g)` in B_1, where g∈C₂, and a prescribed binary cut y of `(G,h)` in X_2. There are exactly two lifts with that fixed source whole: y with bit pairs `(0,g)` and `(1,g+1)`. They are distinct and both have long bit g. Thus Q fails the same active square, despite both its source and target being unital 2-Segal. This second control duplicates **factor decorations**, unlike §6's two witnesses with identical input components; it cannot replace the first control. It is a standard nerve-product regression deliberately kept separate from the actual edge-forgetting proof, not offered as the construction of the original X or as a new scientific contribution.

## 7. Distinctions and evidence boundary

1. Set CULF concerns cartesian naturality squares, not injectivity of F_1 or F_n.
2. Homotopy CULF concerns equivalences to homotopy pullbacks; automorphisms cannot be suppressed by counting representatives.
3. Fixed-source lifting supplies a retained source whole plus an observed fine cut. Recovering that whole from the observation alone is a different, false claim.
4. Fixed-endpoint CFS/kernel uniqueness in the October 29 quotient calculus concerns factorizations of semantic refinement arrows with fixed endpoints. It supplies neither these all-degree maps nor their cartesian squares. Conversely the present theorem does not establish a quotient/refinement comparison or descend arbitrary witness quotients.
5. Reused baseline is the restriction-species edge-forgetting map and fixed-source partition reconstruction. Gálvez-Carrillo–Kock–Tonks, *Decomposition spaces and restriction species* ([arXiv:1708.02570](https://arxiv.org/html/1708.02570)), §1.11 defines CULF by cartesianness on active/generic maps; Theorem 5.8 supplies the restriction-species natural-transformation baseline, and §12.2/Theorem 12.3 distinguishes strict and homotopy pullbacks. The present proof explicitly instantiates the designated original ordered, typed carriers rather than appealing to the name of that theorem; no novelty claim is made for that general mechanism. The scope-specific deliverable is its explicit application to the original typed all-degree cuts, its separate full CUT homotopy interpretation, and the coherent duplicated-witness failure control.
6. P and X are supplied here. C must be a separately replayable finite certificate checking the actual F and P maps, including the original mixed-interface six-vertex case and exhaustive graph/degree floor where required by the dependency package. Finite computation is not an all-degree proof, nor does this note claim all F2 finite or broader F3/I3 obligations accepted.
