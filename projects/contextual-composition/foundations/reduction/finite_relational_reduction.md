# Finite normal forms versus relations: exact reduction

Prepared 1 November 2026. This is a bounded mathematical reduction test of the specific image-factorization/pullback/pushout recipe in the scoping report. It is not a novelty claim, a general no-go theorem for mixed contextads, or adoption/completion of the remaining research contract.

## 1. The presentation and its relation

Replace a monic domain leg by its image. A finite normal form from A to B consists of a subset D ⊆ A, a surjection q:B→Y, and a function f:D→Y. Isomorphic quotient labels do not matter here; equivalently q is a partition of B. Its relation is

    R_f = {(a,b) | a∈D and f(a)=q(b)} ⊆ A×B.

Every row at a∈D is a nonempty complete q-block, because q is onto. Other rows are empty. Thus any two nonempty rows are either equal or disjoint. This is precisely difunctionality: whenever aRb, a'Rb, a'Rb', then aRb'. This equivalence follows directly by applying the displayed implication to an element in the intersection of two rows, in both directions.

Conversely, any finite difunctional relation R⊆A×B has such a presentation. Take D=dom(R), use each distinct nonempty row as a quotient block, partition the unused subset B\im(R) into singleton blocks, and let f(a) be its row. This is well-defined because the nonempty rows are disjoint and cover im(R).

The represented relation determines D and every used q-block. It does not determine how B\im(R) is partitioned. Every partition of that unused subset supplies a presentation of the same relation, and these exhaust the possibilities up to quotient-label isomorphism. This is presentation information, not merely a redundant name for Y.

## 2. Ordinary relational composition is the reference calculation

For a second normal form E⊆B, r:C→Z surjective, g:E→Z, let S⊆B×C be its relation. The ordinary composite is

    T(a,c) iff a∈D and ∃b∈E: f(a)=q(b) and g(b)=r(c).

Relational composition is associative: both bracketings of three relations assert existence of the same two intermediate elements with the same three membership conditions. No chosen quotient or factorization is involved.

Difunctional relations are not closed under this operation. Therefore ordinary Rel is already a compositional enlargement of the arrow semantics, but replacing the original presentations by relations changes the representation and may discard information observable by the proposed normalization recipe. It is not automatically a reduction preserving every demanded datum.

## 3. Exact formula for the proposed binary normalization

The audited recipe first takes the image W=q(E)⊆Y. It then forms the pushout of

    W ← E → Z,

with legs q restricted to E and g. Finally it pulls W back along f. The new domain is

    D' = {a∈D | f(a)∈W}.

The pushout is the quotient of the tagged disjoint union W+Z by the edges

    q(b) ~ g(b), for each b∈E.

Every W-node has at least one incident Z-node. Consequently every pushout class has a Z-node, and the induced quotient C→Z→W+_E Z is onto. Thus the recipe again yields a valid normal form, whether or not composition is associative.

Let M⊆Y×C be the **expanded intermediate relation**

    M(y,c) iff ∃b∈E: q(b)=y and g(b)=r(c).

Unlike T, M includes all active first quotient blocks, including those not in f(D). Its y-row is a union of complete r-blocks.

For any relation V, write cl_df(V) for its least difunctional superrelation. It can be constructed by viewing V as a bipartite undirected graph and completing each nonempty connected component to a complete bipartite relation. This is a closure operator: it is extensive and idempotent; any difunctional superrelation must contain all alternating paths, and the component completion is itself difunctional. Empty rows/columns acquire no new incident edges.

**Exact normalization theorem.** If N denotes the relation of the proposed normalized composite, then

    N(a,c) iff a∈D and cl_df(M)(f(a),c).

**Proof.** Compress the C-vertices of M to their r-blocks. Because each incident row includes the entire r-block and r is onto, this compression preserves the connected-component test between Y-vertices and C-vertices. Its graph is exactly the pushout graph W+Z described above: an edge y—z exists iff some b∈E has q(b)=y and g(b)=z. The normalized output relates a to c exactly when f(a) and r(c) lie in the same pushout component. Its domain condition is exactly that f(a) is an incident Y-node. These are precisely the right-hand conditions. ∎

It follows that T⊆N. Since N is itself difunctional (it is again a normal form), cl_df(T)⊆N. However equality with cl_df(T) can fail: the closure for N is taken before restricting the Y-side along f, and unused Y-nodes can connect previously separate output regions.

**Active-tight corollary.** If W⊆f(D), every active quotient block is selected by some first input, and

    N = cl_df(T).

Proof: replacing each active Y-node by one or more A-nodes with identical adjacency does not change component connectivity or their C-neighbourhoods. Every active Y-node has at least one replacement under the hypothesis. ∎

Global surjectivity f:D→Y is a sufficient, stronger condition. Without active-tightness it is incorrect to describe normalization simply as difunctional closure of the represented relational composite.

**Exact binary soundness test.** For every y∈f(D)∩W, compare its direct neighbourhood M(y) with the C-vertices in its full connected component. The normalized relation equals ordinary relational composition exactly when these sets agree for every such y. Equivalently, none of the alternating paths through used or unused quotient nodes adds a new output to a selected row. In the active-tight case this reduces to T itself being difunctional. This is an exact finite criterion for this recipe, not a general contextad compatibility theorem.

## 4. A binary failure of descent through relation forgetting

Take A={a}, B={0,1,2}. Both first presentations have full domain and f(a) equal to the block {0}. Let their partitions be

    P_fine:   {0} | {1} | {2},
    P_coarse: {0} | {1,2}.

Both denote the same relation {(a,0)}. Their difference concerns an unused quotient block only. Follow either by the pure function

    g(0)=c0,  g(1)=c0,  g(2)=c1,

with identity target quotient on C={c0,c1}.

For P_fine the pushout components retain c0 and c1 separately; the selected row is {c0}. For P_coarse the unused block {1,2} connects c0 to c1, so the selected row becomes {c0,c1}. Thus

    R(P_fine)=R(P_coarse),
    R(P_fine then g) ≠ R(P_coarse then g).

The ordinary relational composite is {(a,c0)} in both cases. It is already difunctional, so even cl_df of that composite remains {(a,c0)}. This proves both that the general closure shortcut is false and that relation forgetting is not a congruence for the proposed binary operation, even under pure postcomposition.

There is a presentation coarsening map P_fine→P_coarse, fixing A and B; it becomes identity/inclusion equality at relation level. Its effect under this recipe can become a strict enlargement after postcomposition. Since the recipe itself is not associative, this is not being promoted to a statement about a functor between completed categories. It is an exact binary non-descent fact.

## 5. Re-explaining the audited associativity failure

Use the scoping example:

- A={a0,a1}; first relation has rows R(a0)={b0,b1}, R(a1)={b2,b3}.
- The second pure function sends b0↦c0, b1↦c1, b2↦c1, b3↦c2.
- The final partial function is defined only at c2 and returns *.

The ordinary intermediate relation has rows

    T(a0)={c0,c1},   T(a1)={c1,c2}.

They overlap but are unequal, so T is not difunctional. The first normalization prematurely completes the connected component, giving both rows {c0,c1,c2}. The final restriction to c2 consequently accepts both a0,a1. If the pure function is first composed with the final restriction, its domain is only {b3}; then the first arrow accepts only a1.

All relevant first quotient blocks here are active-tight, so the closure corollary applies at the offending stage. Ordinary Rel retains T instead of closing it, and both relational bracketings yield exactly {(a1,*)}. The source of failure is a mathematically explicit premature closure, not any failure of relational associativity.

The domains differ over A, hence a different choice of pushout representative or coherent isomorphism of the same normal forms cannot repair this particular recipe.

## 6. What this reduction establishes and what it does not

Established for finite sets:

1. The normal forms denote exactly difunctional relations, with an additional partition of the unused target subset.
2. The proposed binary normalization is expanded difunctional closure before pulling back along the first partial run.
3. Active-tight presentations reduce it to ordinary difunctional closure of relational composition.
4. Forgetting unused quotient blocks is not compatible with the proposed operation, even for a pure continuation.
5. The existing associative relation calculus handles the three-stage example by retaining a non-difunctional intermediate relation.

Thus an enlargement to arbitrary relations is an available semantic repair of this example, but not a preservation theorem for all original presentation distinctions and comparisons. Whether those distinctions are required depends on the declared continuation semantics. Ordinary relational semantics is not obliged to reproduce an overapproximating, nonassociative normalization.

This is a reduction diagnosis, not evidence that a new generalized contextad is necessary. It does not prove the nonexistence of every associative operation on the original normal-form shape. It does not establish a maximal adequate continuation class, a universal mixed law, or novelty. The independent cell audit records more precise hom-category comparison properties; those must not be confused with a horizontal functor for a nonassociative operation.

## 7. Reproducible checks

Run `python verify_finite_relational_reduction.py`. It uses the standard library and explicit error checks that remain enabled under `python -O`.

- All 1,645 pairs of normal forms A→B→C for fixed carrier sizes |A|=2, |B|=3, |C|=2 were checked against the expanded-closure formula.
- All 610 active-tight pairs satisfied the sharper closure formula.
- All 34 difunctional relations on the 2×3 carrier were reconstructed by canonical presentations.
- Closure extensivity, idempotence and difunctionality were checked on all relations on that carrier.
- The binary unused-block example and the original three-stage example passed exactly.

The symbolic proofs above establish the finite-family statements; enumeration supports their implementation and fixed small instances. No probabilistic or floating-point calculation is used. No primary-paper result is being claimed as new on the basis of these checks.
