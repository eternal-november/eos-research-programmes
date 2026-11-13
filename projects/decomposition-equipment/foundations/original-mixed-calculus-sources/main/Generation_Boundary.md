# A genuine horizontal-generation boundary for the original mixed envelope

## Plain-language abstract

Adding arbitrary interface changes and composition to the original calculus does **not** generate every finite-span component used in the enlarged presentation. Interface changes can duplicate witnesses, but cannot give one original component an arbitrarily large number of independently distinguishable input/output channels. More precisely, an exact criterion describes every horizontal object that the original ordinary envelope can generate: its matrix of witness counts must factor through at most b intermediate states, unless it has no graph component. This supplies both explicit missing objects and a constructive certificate for the objects that are available.

One sufficient repair is to permit a graph component to be carried along an arbitrary finite identity interface. Ordinary companions and conjoints then generate all finite-span horizontal objects. This is only an object-generation result: generating all cells and proving the enlarged equations complete remain separate obligations.

## 1. Exact setting and source dependence

Use the ORIGINAL chosen virtual envelope V and ordinary envelope O of `Conservative_Equipment_Envelope.md`, §§1–4, and its separating ordinary equipment E_ord (§8). No additional marking making an old graph assembly universal is imposed. The distinction matters: §10 explicitly says preserving extra pre-existing universal markings is a different relative-presentation problem.

Fix a nonempty finite category K, its regular faithful finite-set realization F, a finite commutative scalar monoid M, and the graph bound N. Put

    b = max { |F(A)| : A an object of K }.

The vertical category B contains arbitrary finite tagged sets and maps. In E_ord a horizontal A→B is `(L,S)`, with L a finite ordered word of graph components and S a finite span A←S→B. A cell consists of a graph forest, a span map and one global scalar. Restrictions leave L unchanged and pull back S; units have empty word; universal composites concatenate words and compose spans by pullback. Original `(G,f:A→B)` interprets as `([G], Γ(Ff))`.

All those constructions, including nullary tuples and scalar labels, are already proved in the cited source. This argument uses that existing model, not a conjectural new model.

A graph-forest isomorphism fixes its graph word literally: the ordered occurrence-allocation maps of inverse forests must be inverse monotone bijections, hence identities; each remaining unary graph cut fixes its graph. In particular `[empty graph]` is NOT the empty word, even though there is a nullary assembly from the latter to the former. This is exactly §10 of the source.

## 2. Boolean rectangle-cover invariant

For a span S:A←S→B write

    supp(S) = { (a,b) : some s∈S has endpoints (a,b) }.

For a finite relation R⊆A×B, let rc(R) be the least k such that R is the union of k rectangles X_i×Y_i (including rc(empty)=0). This invariant forgets witness multiplicities; that is enough for the obstruction.

**Lemma 2.1 (restriction).** For f:A′→A and g:B′→B,

    supp(S[f,g]) = (f×g)^(-1)(supp(S)),
    rc(supp(S[f,g])) ≤ rc(supp(S)).

Proof. A point in the restricted apex is precisely (a′,s,b′) with f(a′)=left(s) and g(b′)=right(s). The inverse image of X×Y is f^(-1)(X)×g^(-1)(Y). These statements hold for noninjective, nonsurjective and empty maps.

**Lemma 2.2 (composition).** For finite relations P⊆C×A, R⊆A×B and Q⊆B×D,

    rc(P;R;Q) ≤ rc(R).

Proof. If R=⋃_{i≤k} X_i×Y_i, then

    P;R;Q = ⋃_{i≤k} P^(-1)[X_i] × Q[Y_i],

where P^(-1)[X]={c:∃a∈X, (c,a)∈P} and Q[Y]={d:∃b∈Y, (b,d)∈Q}. Existential witnesses on the two sides are independent once the rectangle index is fixed. The support of pullback composition of spans is exactly relational composition. Thus composing on either side with ANY finite span cannot increase the middle span's rectangle-cover rank.

**Lemma 2.3 (primitive and diagonal).** Every original primitive span Γ(Ff) has rectangle-cover rank at most |F(dom f)|≤b. The diagonal Δ_E has rectangle-cover rank exactly |E|.

Proof. Each primitive apex element gives a singleton rectangle. A nonempty rectangle contained in Δ_E has exactly one diagonal point: two distinct points would force an off-diagonal pair. Singleton diagonal rectangles attain the bound.

## 3. The original-envelope obstruction

**Theorem 3.1.** If an O-horizontal expression interprets to graph word `[G]`, its interpreted span support has rectangle-cover rank at most b. Consequently, if |E|>b, the horizontal

    D_G(E) = ([G], E ←id E →id E)

of E_ord is not isomorphic to the interpretation of any O-horizontal expression. This holds for every allowed graph G; in particular take G to be a one-vertex graph. It also holds for the smaller V grammar interpreted in E_ord.

Proof. The graph word of a horizontal expression is obtained by placing one letter at each occurrence of an original horizontal, no letters at a fresh unit, preserving words under restriction, and concatenating them under composition. Its word length therefore equals its number of original-horizontal leaves. A singleton word forces exactly one such leaf, whose graph is G. All other branches have no original leaves. Old empty-graph primitives cannot hide in those branches: each still contributes a letter.

Follow the unique original leaf to the root of the expression. At the leaf the support rank is at most b by Lemma 2.3. A restriction preserves the bound by Lemma 2.1. At each composite, exactly one child contains the leaf. Compose that child's span with the remaining children on the left and right; Lemma 2.2 preserves the bound. This structural induction allows arbitrary nesting, singleton composites, noninvertible restrictions and empty spans.

If an arbitrary interpreted expression is isomorphic to D_G(E), projection of that cell and its inverse to the graph-forest category first forces its word to be exactly `[G]`. Projection to spans forces mutually inverse endpoint-preserving apex maps, so the span support equals Δ_E. Lemma 2.3 then gives |E|≤b, a contradiction. Scalars do not weaken the argument: projection of inverse cells still gives inverse span maps and inverse graph forests. ∎

**Corollary 3.2 (exact carrier threshold).** For every allowed graph G and finite tagged set E, the carrier D_G(E) is isomorphic in E_ord to the interpretation of an original V-horizontal expression (and hence an O-horizontal expression) **if and only if** |E|≤b.

Proof. Necessity is Theorem 3.1. For sufficiency, choose an old interface A attaining |F(A)|=b and an injection i:E→F(A), available in the full finite-set vertical category B. Take the old component (G,id_A), whose interpreted span is the identity on F(A), and restrict it along (i,i). Its apex consists of triples (e,x,e′) with i(e)=x=i(e′). Injectivity forces e=e′; conversely each e determines exactly the triple (e,i(e),e). This is an endpoint-preserving bijection with the identity span on E, and the graph word remains [G]. This also covers E empty. ∎

This exact threshold concerns the identity-span carrier family. The support-rank bound for general spans is necessary but not sufficient in general; Section 4 gives the exact stronger criterion retaining witness multiplicities.

**What this establishes.** The canonical interpretation from the free original ordinary envelope into its explicitly enlarged finite-span model is not essentially surjective on horizontal objects. Thus the enlarged local presentation cannot be imported as a presentation of the original free envelope merely by adding the original envelope's restriction/unit/composite constructors. This does not contradict conservativity, and does not assert a failure of equality reflection or any particular old-profile fullness claim.

**What cannot be substituted for the proof.** Apex cardinality alone is NOT invariant: noninjective restriction may greatly enlarge an apex. The support's rectangle-cover bound is the invariant. Nor may old empty-graph components be identified with fresh units: the occurrence allocation prevents this, including in the presence of nullary cells.

## 4. Complete ordinary horizontal-image criterion, retaining multiplicities

The support obstruction admits a sharper version that classifies the ENTIRE horizontal essential image of O→E_ord, not just the diagonal carriers. This section does not assert a corresponding converse for V, whose grammar lacks ordinary composites.

For a span S:A←S→B define its nonnegative integer multiplicity matrix

    n_S(a,b) = |{s∈S : left(s)=a, right(s)=b}|.

For a finite matrix X over N₀ let rank_N(X) be its least factorization width: the least k≥0 for which X=P Q with P∈N₀^(A×k), Q∈N₀^(k×B). The zero matrix has width zero. This is nonnegative INTEGER factorization rank, not real rank, nonnegative-real rank or Boolean rectangle rank. A factorization always exists, for example X=X I_B. Two finite spans with fixed endpoints are isomorphic if and only if their multiplicity matrices agree: choose a bijection in each finite endpoint fibre.

**Lemma 4.1 (matrix semantics).** Span composition multiplies multiplicity matrices over N₀. Restriction along f:A′→A, g:B′→B sends X to F_f X F_g^T, where F_f(a′,a)=1 iff f(a′)=a, and similarly F_g(b′,b)=1 iff g(b′)=b.

Proof. A composite witness over (a,c) is a pair of witnesses with a shared b, so its count is Σ_b n_S(a,b)n_T(b,c). A restricted witness over (a′,b′) is exactly an old witness over (f(a′),g(b′)). These formulas count every witness, not just support, and apply when any interface or apex is empty. ∎

**Lemma 4.2 (bottleneck).** If X=P Q has width k, then U X V=(U P)(Q V) has width at most k for any compatible nonnegative integer matrices U,V. An original graph span Γ(Fh) has width at most |F(dom h)|≤b, by factoring its multiplicity matrix through its own apex.

**Theorem 4.3 (complete horizontal essential image).** A horizontal (L,S) of E_ord is isomorphic to the interpretation of some O-horizontal expression if and only if

    L is the empty word, OR rank_N(n_S) ≤ b.

Necessity. Suppose L is nonempty. Its expression has at least one original-horizontal leaf, since units contribute no graph letters and restrictions/composition cannot introduce letters. Choose any such leaf. Its matrix factors through at most b points. Follow that leaf to the root: at restriction nodes use Lemma 4.1 and the bottleneck lemma; at composite nodes multiply by the matrices of all siblings to the left and right. This gives a factorization of the final matrix through the same number of points. Other siblings may have their own graph letters and arbitrary witness multiplicities; no independence or singleton-word assumption is used. If only isomorphism to (L,S) is given, graph-word rigidity preserves L and a span isomorphism preserves n_S.

Sufficiency for the empty word. Every finite span A←l E→r B is interpreted by l^*;r_*, with l^*=I_A[id_A,l] and r_*=I_B[r,id_B]. Both have empty graph word and their composite span is canonically the desired S.

Sufficiency for a nonempty word L=[G₁,…,G_t]. Let n_S=P Q have width k≤b. Choose an old interface A₀ whose finite realization C=F(A₀) has cardinality b, inject the factor-index set into C, and pad P,Q with zero columns/rows to obtain matrices indexed by C. Realize these matrices as finite spans P̂:A→C and Q̂:C→B: for each matrix entry create precisely that many distinct apex witnesses. By the preceding empty-word construction both spans are generated without original graph leaves. Between them compose the old components

    (G₁,id_A₀), …, (G_t,id_A₀).

Each has span matrix I_C and the indicated singleton graph word. The complete expression

    P̂ ; (G₁,id_A₀) ; … ; (G_t,id_A₀) ; Q̂

therefore has graph word L and span matrix P I_C⋯I_C Q=n_S. The fibrewise finite-span isomorphism gives the required horizontal isomorphism in E_ord, with identity graph forest and scalar 1. This includes k=0 and empty endpoints. ∎

**Positive certificate and compiler.** A proposed nonnegative integer factorization P Q=n_S of width at most b is a sufficient horizontal-generation certificate. The proof explicitly compiles it into the original O grammar. From a concrete generated term with nonempty graph word, choosing an old leaf and propagating the matrix factors upward extracts such a certificate. Checking an explicitly supplied matrix factorization is ordinary exact integer matrix multiplication; the theorem makes no efficiency claim for finding a factorization, for constructing huge apex sets encoded by binary integers, or for deciding equality of arbitrary cell terms.

**Why Boolean rank is insufficient.** The matrix [[1,1],[1,2]] has full rectangular support (Boolean rank one) but rank_N exactly two. Width one would give entries u₁v₁=u₁v₂=u₂v₁=1, forcing u₁=u₂=v₁=v₂=1 and contradicting u₂v₂=2. Width two is given by X I₂. Thus, when b=1, this span with any nonempty graph word is not generated despite satisfying the support bound. For terminal K the regular realization has b=1. The corresponding span has five actual witnesses and cannot accompany any nonempty graph word in the generated image, although its support passes the Boolean test. Removing its duplicate witness gives the all-ones matrix, which factors through one point and is generated. The exact criterion therefore detects witness multiplicity, not just observable endpoint support.

For a diagonal carrier n_S=I_E, rank_N(I_E)=|E|: any nonnegative factorization gives a support rectangle cover of width at most its middle dimension, and singleton diagonal factors attain the bound. The exact threshold of Corollary 3.2 follows again.

This is a complete semantic IMAGE criterion on horizontal objects. It is not a normal-form theorem for syntactic horizontal expressions, not fullness on cells, and not a claim that every semantic isomorphism lifts to an isomorphism in the source envelope. The target carrier or arbitrary span is an object of E_ord, not generally an object named in the original syntax.

## 5. Explicit sufficient horizontal extension

Adjoin, for every allowed graph G and every finite tagged set E, a new horizontal carrier D_G(E):E→E with the above interpretation. This is one sufficient schema, not a claim of unique minimality or a proved universal initial repair.

For any finite span S=(A←l E→r B), the needed empty-word horizontals already exist from restrictions of units:

    l^* = I_A[id_A,l] : A→E,
    r_* = I_B[r,id_B] : E→B.

Their interpreted spans are respectively A←l E→id E and E←id E→r B. Consequently

    l^* ; D_G(E) ; r_*

interprets, up to the canonical pullback-coordinate isomorphism, as `([G],S)`.

This also generates every word-span horizontal of E_ord up to isomorphism. For a nonempty word `[G1,…,Gk]`, compose the expression for `([G1],S)` with D_G2(B),…,D_Gk(B). For an empty word, use l^*;r_* alone. These statements include E or B empty. All graph-carrier expressions must still be regarded as formal extra objects until an enlarged source presentation is specified.

**Bounded-primitive corollary.** More generally, an extension using the same restriction/unit/composition grammar cannot be horizontally essentially surjective if all its primitive horizontals with singleton graph word have span support rank bounded by a common constant c. A term with singleton graph word can contain only one such primitive and any number of empty-word primitives; primitives with longer words cannot occur. The same induction bounds its rank by c. In particular no uniformly bounded-apex replacement family suffices, even when arbitrary empty-word spans are freely available.

The obstruction proves that any horizontally essentially-surjective extension must allow singleton-graph supports of unbounded rectangle-cover rank as E varies. It does not prove that exactly this schema is necessary; alternative primitive families or constructors might provide the same unbounded capacity.

## 6. Remaining cell-level burden

This schema generates objects, not arbitrary apex maps or graph/scalar cells. A full comparison with `Extended_Local_Presentation.md` still needs:

1. explicit generating cells for maps between the new carriers and their span factorizations;
2. equations relating those cells to original graph cuts and scalars;
3. compatibility with the actual chosen restrictions, units and composites, retaining nullary common boundary maps;
4. a proof of full cell generation and equality completeness, or an explicitly limited comparison theorem.

Nothing here establishes items 1–4. Nor does this prove exact transport of cuts along arbitrary noninvertible interface maps; that is a separate recoverability obstruction and repair question.

## Verification status

Author proof from the existing separating equipment and a finite-relation invariant; not Lean-formalized. A small exhaustive script tests the two invariant operations on all binary relations over a two-element set and checks diagonal ranks through size four. The script also checks all 81 two-by-two matrices with entries 0, 1, 2 for exact integer factorization width and verifies the multiplicity counterexample. Those checks illustrate the proof and are not its justification.
