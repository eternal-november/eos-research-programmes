# Presentation cells, relations and corelations: exact bounded reduction

1 November 2026. This note proves elementary representation and comparison facts for the finite mono/surjection normal form. It is not a novelty claim, a construction for arbitrary contextads, or a claim that a nonassociative recipe is already a category. The abstract mixed problem remains separate.

## 1. Presentation categories and native squares

Fix finite sets A,B. Up to isomorphism of quotient labels, a presentation is P=(X,pi,f), where X is a subset of A, pi is a partition of B, and f maps each x in X to one block of pi. This is the normal form A <- X -> Y <- B with left inclusion and right surjection, using Y=pi. In particular every chosen output block is nonempty. If B is empty then X must be empty.

For fixed endpoints, a square P→P' exists exactly when:

1. X⊆X';
2. pi refines pi';
3. f(x)⊆f'(x) for every x∈X.

It is unique when it exists. The domain map is forced by the inclusion and the quotient map is forced by the surjection. These give an ordinary poset after quotient labels are normalized, and a preorder with unique isomorphisms before that normalization.

For endpoint maps a:A→A' and b:B→B', the square conditions are a(X)⊆X', every block of pi maps into a block of pi', and b(f(x))⊆f'(a(x)). These are the both-forward native grade directions: CM Definition 3.17, equations (3.3.15–16), and Example 6.4, printed pp22,65. Vertical composition exists. Horizontal composition is not inferred from this data.

## 2. Ordinary relational denotation and the exact local adjunction

Define E(P)={(x,b): x∈X and b∈f(x)}⊆A×B. Its nonempty rows are blocks of one partition, hence any two rows are equal or disjoint. Equivalently E(P) is difunctional. Conversely every finite relation with equal-or-disjoint nonempty rows has such a presentation: use its domain X, its distinct row blocks, and any partition of the unused output elements.

Thus the image is exactly the difunctional relations. The domain and active row blocks are visible; the partition on unused B elements is invisible. The fibre over a relation R is precisely the partition poset of B\ran(R).

Let DRel(A,B) be the poset of difunctional relations ordered by inclusion. E defines an ordinary functor from the fixed-endpoint presentation poset to DRel(A,B). It is faithful in the ordinary categorical sense (all hom-sets have at most one element), but generally neither full nor conservative. For example A={a}, B={0,1,2}, f(a)={0}; partitions {0}|{1}|{2} and {0}|{1,2} denote the same relation. There is a noninvertible coarsening from the first to the second, and no reverse square. E sends that arrow to an identity, and the reverse relational identity has no preimage.

Define F(R) to have the distinct nonempty rows of R as blocks and each unused output as a singleton. Then

    F(R) ≤ P  iff  R ⊆ E(P).

Proof: the forward implication follows from the square conditions. Conversely inclusion gives domain inclusion and places every row block of R inside the corresponding target row block; each unused singleton automatically lies in a unique target partition block. This supplies the unique required quotient square. Therefore F is left adjoint to E and EF=id. This is a local adjunction for an ordinary presentation category, NOT a mixed horizontal functor or an adjunction between already-defined mixed double categories.

The denotation is not a congruence for the tested normalization. In the example above, postcompose with the pure function g:B→{c0,c1}, g(0)=g(1)=c0 and g(2)=c1. The discrete unused partition produces only (a,c0); the coarse unused block {1,2} forces c0 and c1 together in the pushout and produces both (a,c0),(a,c1). The initial relation was identical. Hence forgetting unused blocks does not preserve all allowed pure postcontinuations of this recipe.

## 3. Corelations retain all the normal-form data

A Set corelation A⇝B can be represented by a partition of the tagged disjoint union A+B. Composition glues the middle B, takes the generated equivalence relation, then restricts its components to the outer endpoints; components with no outer endpoints disappear. This is the standard jointly-surjective cospan construction. Its category is established; Fong–Zanasi §2 gives the factorization construction and §4.4 distinguishes it from ordinary relations in Set.

Define I(P) to have, for each partition block y of pi, the block

    {tagged x∈X: f(x)=y} union {tagged b∈y},

and also one singleton block for each a∈A\X.

This retains unused output blocks as output-only blocks. Its image consists exactly of partitions whose input-only blocks are singletons. The inverse recovers X as the inputs lying in a block meeting B, pi as the induced partition on B, and f from that block. Thus I is injective on normalized presentations.

For cells, define a corelation square over (a,b) by requiring the tagged map a+b to preserve equivalence. This is the usual quotient-cospan square condition; vertical composition and compatibility with gluing follow by preservation of the generating identifications. For I(P),I(P'), this condition is equivalent to the presentation-square conditions of §1. An active input is connected to some output; its image must remain active. Output equivalence supplies the quotient map. Commutativity follows from the same block condition. Conversely a presentation square preserves every generating block. Hence I is fully faithful on this individual-arrow-and-square data, including arbitrary endpoint maps. This statement does not equip its image with a horizontal composition it lacks.

## 4. The failed normalization is precisely corelation composition followed by pruning

Let N send a corelation partition to the partition obtained by splitting every input-only block into singleton inputs, leaving all blocks meeting B unchanged. Then N is monotone, idempotent, and IN(Q)≤Q in the refinement order. For any normal-form partition I(P),

    I(P)≤Q  iff  I(P)≤IN(Q).

Indeed every nonsingleton block of I(P) meets the output, so its containing block of Q is retained unchanged. Singleton input blocks impose no obstruction. Thus I is left adjoint to N on each hom-poset: this is a coreflection onto the normal forms, not a reflection in the opposite direction.

For presentations P:A⇒B and Q:B⇒C, the image-factorization/pullback/pushout recipe in the scoping report is exactly

    P star Q = N( I(P) ; I(Q) ),

where semicolon means corelation composition in execution order.

Proof. Write P as X⊆A, q:B↠Y, f:X→Y and Q as U⊆B, d:C↠V, g:U→V. Corelation composition has a bipartite graph with vertices Y and V and one edge q(u)—g(u) for each u∈U. Its output-bearing components are exactly the components of W+_U V, where W=q(U). Every V vertex has an output because d is onto. A first input x lies in such a component exactly when f(x)∈W, which is the domain selected by the old pullback. All remaining active inputs form input-only blocks grouped by their old Y vertex; N splits these. Originally inactive inputs were already singleton. This is exactly the old normal form, including its quotient and body maps.

This reduces the failure to premature pruning in an established associative calculus. N is not multiplicative. The scoping example's g;h produces an input-only block {b1,b2}; pruning it before precomposing with f destroys a connection that f can attach to a surviving output. The two normalized bracketings then have different domains. The relation to a coreflection explains the failure, but does not repair the old operation by itself: homwise adjoints do not automatically compose horizontally.

## 5. Why the corelation enlargement is not the contract solution

Corelations supply associative composition while retaining all original presentation/square data. They add input-only correlations, which the old normal form cannot express. These are connectivity data, not automatically an assertion that a program is enabled.

They preserve the content-only jointly-surjective cospan control: if the source domain is total, every source is attached to an output in each one-sided stage, and ordinary cospan/corelation composition agrees with that control. They do NOT preserve the context-only partial-function control under I.

Minimal witness: let g:{a0,a1}→{b} be constant and h:{b}⇀{c} be nowhere defined. Their partial-function composite is nowhere defined, represented by singleton a0,a1,c blocks. But I(g);I(h) retains the input-only block {a0,a1}, plus singleton c. Thus I is not a horizontal functor preserving the existing partial-map composition even within that one-sided subcase. Applying N restores that isolated composite, but N fails to commute with later composition as above.

Conversely ordinary relations preserve partial-function composition, but not the content-only quotient/pushout control: the two unused-partition presentations and pure g in §2 already show this, with both first arrows total. Tabulating ordinary relations as jointly-monic spans likewise forgets the unused output partition. Arbitrary spans retain execution witnesses of relational composition, but do not make that forgotten quotient information reappear. Thus simply saying “use spans/relations/corelations” requires selecting which interpretation and preservation requirements are intended.

This is not a claim that no other existing equipment or decorated construction can preserve the desired data. It shows precisely what these particular reductions do and do not preserve. In particular the nonassociative original recipe cannot be the domain of a composition-preserving functor in the first place.

## 6. Linear positive comparison: the loss disappears, but the semantics is known

For finite-dimensional vector spaces over a field, use X≤A, a surjective linear q:B→B/K, and linear f:X→B/K. Interpret the presentation as the linear relation

    R={(a,b): a∈X, f(a)=b+K}≤A⊕B.

Every linear relation admits this normal form: X=pr_A(R), K={b:(0,b)∈R}, and f(a)=b+K for any (a,b)∈R. This is well-defined and linear. Conversely these data recover R. Unlike the Set case, the kernel K is always observed in the row at zero, so there is no hidden unused-output partition.

For endpoint linear maps a:A→A',b:B→B', preservation of relations implies a(X)⊆X' and b(K)⊆K' (use the zero row), hence the unique quotient map and commuting body square. The converse is immediate. Thus normalized linear presentations and linear relations have exactly the same squares. This is an explicit double-level comparison, not a generic claim that all retained-cell issues disappear.

The tested composition formula also agrees with relational composition here. For the next domain U≤B and body g:U→C/L, the crossing image is q(U), with kernel U∩K. The pushout of U↠q(U) with g is (C/L)/g(U∩K), and the new domain is {a∈X:f(a)∈q(U)}. For a chosen u∈U with q(u)=f(a), the resulting output coset is g(u)+g(U∩K). These are precisely all outputs obtained by existentially choosing an intermediate u; adding L recovers the C-level relation. Hence the normal recipe is associative in this linear setting and the normalized presentation double category is equivalent to the familiar linear-relation double category. This is a direct elementary verification of a known semantic class, not a new contextad theorem.

Fong–Zanasi Corollary 3.4 proves the abelian relation/corelation comparison under epi/mono hypotheses, and §4.7 treats vector-space subspaces. The linear calculation here is consistent with that established baseline. It does not solve the requested broad dependent contextad interaction or independently establish a novel generalization.

## 7. Verification and source boundaries

`check_presentation_cells.py` runs with ordinary Python and with `python -O`; all checks use explicit failure tests, not optimization-disabled assertions. It checked 22,764 finite instances of F⊣E, 27,380 full-faithfulness equivalences for I, 35,951 coreflection comparisons, and 428 binary normalization comparisons (all source/middle/target sizes≤2 for the latter). It also checks the minimal one-sided failure and the original nonmultiplicativity witness. The finite enumeration supports the symbolic proofs above; it does not prove the general linear statement by enumeration.

Primary sources inspected for the imported background:

- Capucci–Myers, Contextads as Wreaths, Def3.17 pp22–24 and Examples6.4–6.6 p65: native cell direction, partial/span context and cospan content controls. https://arxiv.org/pdf/2410.21889
- Fong–Zanasi, Universal Constructions for (Co)Relations, LMCS14(3:14), 2018, §2, Corollary3.4 pp10–11, §4.4 and §4.7: categorical (co)relation construction, Set warning, abelian/linear positive control. https://arxiv.org/pdf/1710.03894

The local adjunctions, exact normal-form/corelation pruning equality, and explicit cell comparison are elementary deductions supplied with proofs here. No historical priority is claimed for them. The earlier Štěpán recognition audit is relevant as an anti-novelty baseline, but no additional theorem from it is needed for these concrete deductions.
