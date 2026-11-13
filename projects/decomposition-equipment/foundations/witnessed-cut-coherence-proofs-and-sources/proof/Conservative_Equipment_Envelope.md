# Conservative chosen equipment envelopes of the original graph calculus

Author proof for the bounded infrastructure target, submitted 25 October 2026. Editorial delivery copy: current mathematical scope and review status are in [ScopeAndStatus.txt](../ScopeAndStatus.txt). Original and delivered hashes are recorded in SourceManifest.txt. Preliminary-target and status references have been normalized; mathematical proof content is unchanged. This is not a proof of the central coupled quotient theorem.

One explicit typing correction to the target is recorded: B is a SMALL FULL CATEGORY OF FINITE TAGGED SETS, not necessarily a skeleton. It contains distinct tagged F(A) for distinct old interfaces A. This avoids identifying old interface names merely because they have the same cardinality. Chosen finite pullbacks exist in B. Nothing says the induced vertical 2-category is locally discrete.

## Theorem and exact strength

For every N>=6, finite category K, finite commutative monoid M, and the fixed regular realization F of K in B, the original C5 local presentation has a free chosen virtual-equipment extension V and a separately free chosen ordinary-equipment extension O. Both have underlying vertical category B. In the strict chosen convention, restriction of interpretations gives an ISOMORPHISM OF CATEGORIES between choice-preserving interpretations with Cruttwell-Shulman transformations and interpretations of the original local presentation. With strong preservation rather than literal preservation of choices, this becomes an equivalence of categories, with explicit coherent comparison maps below.

The maps from the original calculus C into V and O reflect equality on every original full profile, preserve and reflect equality of actual old refinement tuples, and reflect the existence of unary globular isomorphisms between original components. No general fullness or classification of all new original-profile cells is claimed.

The proof consists of an explicit finite-term construction, an all-context universal-property proof, a transformation-extension argument, and independent separating semantic models. The standard categorical infrastructure is credited, not counted as novelty: virtual double categories and transformations follow Cruttwell and Shulman, *A unified framework for generalized multicategories*, Definitions 2.1 and 3.1; strong opcartesian cells and cartesian restrictions are their Definitions 5.1 and 7.1. Primary source: https://arxiv.org/abs/0907.2460 . Our constructors below give the particular free presentation and the witness-sensitive separating comparison; they do not assume the required free object exists.

## 1 Input presentation and interface realization

Let Sigma_C5 and E_C5 be the original C5 generators and seven local rotation/unit/scalar equation schemes, with the exact full component profiles and scalar conventions in the supplied source. We use this LOCAL presentation, not a list of every semantic operation and true equation. The accepted original comparison identifies its presented calculus with C(N,K,M).

For each A in K put

    F(A) = { (C,u) : C an object of K and u:C->A },
    F(h)(C,u)=(C,h u).

Tag the set additionally by its codomain A when selecting its finite-set representative. If F(h)=F(k) for parallel h,k:A->B, evaluation at (A,id_A) gives h=k. Hence F is faithful. Distinct A have distinct chosen tagged representatives. Functoriality is category associativity and identities.

The ordinary vertical category B and its entire composition table are fixed input, not reconstructed from the horizontal calculus. A target interpretation includes a functor v:B->E_vertical. If the task fixes the target interface realization, take the corresponding fibre of this interpretation category; the construction below works in either convention.

## 2 Horizontal terms

For V the horizontal expressions, with their endpoints, are generated inductively by:

1. each original component W:A->B, now based at F(A),F(B);
2. a fresh unit expression I_A:A->A for every A in B;
3. H[f,g]:A'->B' whenever H:A->B, f:A'->A and g:B'->B.

There are NO equations on these horizontal expressions. In particular H[id,id] need not be literally H, and an old empty-graph component is not literally I_A. Their appropriate universal comparison isomorphisms will be cells, not covert equalities of types.

For O add a horizontal expression C(H1,...,Hn):A0->An for every nonempty composable path; the chosen zero-length composite is I_A. A singleton composite is allowed as a fresh expression. All restrictions and units are again available for all new expressions. Both grammars produce sets because B and the original presentation are small and the terms are finite.

O can be built directly from the same original local generators and this larger grammar. It is consequently not a tautological presentation using all cells of a preconstructed V. The canonical map V->O follows from V's interpretation property after O is constructed. That map realizes the relative ordinary-envelope property because interpretations of V are exactly interpretations of the original presentation.

## 3 Typed cell terms and equations

Write a cell type as

    alpha : (P1,...,Pn) => H ; (f,g),

where the source path has interfaces A0,...,An, H:B0->B1, and f:A0->B0, g:An->B1. For n=0 its source is the SPECIFIED interface A0; f and g can be different vertical arrows with this common domain.

The constructors in both grammars are:

* Original generator cells with their original globular profiles.
* Identity cell 1_H for every horizontal expression.
* Fully typed VDC substitution. Given an outer cell with m source slots and inner cells at those slots, one retains the ENTIRE interface-map family u_0,...,u_m, so adjacent inner boundaries agree. In the m=0 case the family still contains u_0. This gives nullary vertical whiskering alpha<u>: its boundary arrows are the old boundaries composed with u. It is not erased as an 'empty tuple'.
* A cell kappa_(H;f,g):H[f,g]=>H with boundaries f,g.
* A nullary unit cell eta_A:()=>I_A with identity boundaries.
* For any cell alpha with target H and boundaries f u,g v, a restriction-factor term L_(H;f,g;u,v)(alpha), with target H[f,g] and boundaries u,v.
* For any cell alpha with source path r,s, where r ends and s begins at A, a unit-factor term U_(r,A,s)(alpha) whose source is r,I_A,s. The two outside vertical boundaries and target are unchanged. The context r,s can have any finite lengths, including zero.

For O add:

* mu_p:p=>C(p), with identity boundaries, for every nonempty path p;
* for any cell alpha with source r,p,s, a composite-factor term Q_(r,p,s)(alpha), whose source is r,C(p),s and whose other type data are unchanged.

Impose the VDC associativity and identity equations, including the nullary-whiskering cases, and all original E_C5 equations. Impose the following beta and eta schemes at EVERY well-typed occurrence:

    kappa . L(alpha) = alpha,
    L(kappa . beta) = beta;                              (R)

    U(alpha)[1_r,eta_A,1_s] = alpha,
    U(beta[1_r,eta_A,1_s]) = beta;                        (U)

    Q(alpha)[1_r,mu_p,1_s] = alpha,
    Q(beta[1_r,mu_p,1_s]) = beta.                         (C)

The last scheme is only in O. These equations carry the displayed source-context and boundary parameters; they are not equations on an untyped free monoid. The congruence is the least parallel equivalence relation stable under ALL cell constructors, including L,U,Q, containing those schemes. The quotient cell sets, horizontal expressions and fixed vertical B define V and O.

This construction does not require a rewrite system, termination or a normal-form theorem. It is a small term quotient. Its correctness is proved next rather than being assumed from the word 'free'.

## 4 The equipment axioms and all-context universality

VDC substitution is well-defined on the quotient because the equivalence is a constructor congruence. Its identities and associativity hold by the imposed VDC laws. The nullary case retains the given common vertical arrow, as required by the standard VDC definition.

For any kappa_(H;f,g), postcomposition gives a function from cells into H[f,g] with boundaries u,v to cells into H with boundaries fu,gv, at every arity and every source path. The inverse is L. The two equations (R) are exactly the two inverse laws. Thus kappa is cartesian with the ACTUAL all-arity universal property. There is no restriction to globular or unary source cells.

Similarly insertion of eta_A into a specified source slot gives a function from cells with source r,I_A,s to cells with source r,s. Its inverse is U. Equations (U) prove this is a bijection for arbitrary r,s, targets and outside boundaries. Therefore eta_A is strongly opcartesian as a nullary cell, not merely weakly opcartesian at an empty surrounding context. V is a virtual equipment.

In O, the same argument with (C) proves that each mu_p is strongly opcartesian in every surrounding path. Together with the n=0 unit case, every finite horizontal path has a universal composite. Thus O is an ordinary equipment in the representability sense. The induced associators and unitors are obtained by factoring the same flattened source path through the corresponding iterated mu cells. Any two coherence composites have the same precomposition with that universal flattened cell, hence are equal. This proves their pentagon, triangle, and higher finite rebracketing coherence, rather than choosing unrelated isomorphisms.

Restrictions along identities and composites likewise have canonical invertible comparison cells: two successive cartesian restriction cells compose to a cartesian cell, and any two such cells with the same target and boundary data have unique inverse comparison maps. Coherence follows because their composites have identical postcomposition with the target cartesian cell. No horizontal expression equality is inferred.

## 5 Interpretation on objects and cells

Let E be a chosen virtual equipment and choose a presentation interpretation: a vertical functor v:B->E_vertical, one horizontal image for every original component, and images for the original generators satisfying E_C5. Interpret horizontal expressions recursively using the chosen units and restrictions of E. In the ordinary case use E's chosen composites as well.

Interpret identity and substitution terms by E's operations, kappa,eta,mu by its chosen universal cells, and L,U,Q by their UNIQUE universal factorization maps. Every equation (R),(U),(C) holds because the corresponding maps are inverse bijections. VDC and old local equations hold by assumption. Hence interpretation descends to the quotient.

Conversely a strictly choice-preserving equipment morphism restricts to such presentation data. The extension is unique on horizontal terms by their grammar. It is unique on kappa,eta,mu by choice preservation and on L,U,Q because those are universal factors. Induction on cell terms then gives uniqueness on all cells. Extension and restriction are literal inverses on the objects of the claimed interpretation categories.

## 6 Extension of transformations

Use exactly the standard cell-natural transformation convention. Between presentation interpretations F and G, the input transformation consists of a natural transformation tau on their vertical functors and, for each ORIGINAL horizontal H:A->B, a unary cell tau_H:FH=>GH with boundaries tau_A,tau_B, satisfying naturality for the original generators. Old local equations introduce no new condition once generator naturality and substitution naturality are proved.

Extend tau to new horizontal expressions recursively.

* Restriction r=H[f,g]. Compose F(kappa_r) with tau_H. Its outer boundaries are tau_A Ff and tau_B Fg, which equal Gf tau_A' and Gg tau_B' by vertical naturality. Factor it uniquely through G(kappa_r), defining tau_r. Thus

      G(kappa_r) . tau_r = tau_H . F(kappa_r).          (6.1)

* Unit I_A. Whisker G(eta_A) by the vertical arrow tau_A to obtain a nullary cell at FA with target GI_A. Factor it uniquely through F(eta_A), defining tau_(I_A). Thus

      tau_(I_A) . F(eta_A) = G(eta_A)<tau_A>.          (6.2)

* Composite C(p), in O. Form G(mu_p)[tau_(P1),...,tau_(Pn)], whose source is Fp. Factor it uniquely through F(mu_p), defining tau_(C(p)). Thus

      tau_(C(p)) . F(mu_p)
        = G(mu_p)[tau_(P1),...,tau_(Pn)].             (6.3)

These formulas retain all internal vertical components of tau. They do not require them to be identities or invertible.

We prove cell naturality by induction on cell terms. It is given for old generators, immediate for identities, and follows from VDC associativity for substitution; the m=0 case uses vertical naturality to compare the retained common boundary arrow. Naturality of kappa,eta,mu is (6.1)-(6.3).

For a restriction-factor term L(alpha), compare the two desired naturality composites and postcompose them with G(kappa). Using (6.1) and the beta law (R), their images become the two composites in the already known naturality of alpha. Cartesian uniqueness of G(kappa) therefore proves equality of the factors.

For U(alpha), precompose the two desired composites with F(eta) at the specified source slot. Equation (6.2), the beta law (U) and naturality of alpha identify the results. The all-context opcartesian uniqueness of F(eta) proves the original equality. For Q(alpha), the identical argument uses F(mu), (6.3), and (C). This proves naturality for EVERY cell term, including arbitrary surrounding contexts and iterated factors.

The extension is unique: naturality of kappa,eta,mu forces (6.1)-(6.3), and their universal properties uniquely determine each new horizontal component. Thus restriction and extension are inverse on transformations as well as functors. Identities and vertical composition of transformations are preserved by uniqueness from their old components. Whiskering and target naturality follow by the same argument. This proves the stated isomorphism of interpretation categories, not merely a bijection of hom-sets of objects.

## 7 Change of universal choices

Suppose the SAME underlying target equipment is equipped with two choices of units/restrictions/composites. Given the same original interpretation, evaluate the term grammar with each choice. There is a unique transformation between the resulting evaluation functors whose vertical part and original-horizontal components are identities: define its remaining components by (6.1)-(6.3). The reverse construction gives its inverse, since both composites restrict to the identity old data and extension is unique.

For three sets of choices, the direct comparison equals the composite of the other two, again by uniqueness from the old data. This gives actual coherent comparison isomorphisms, not an appeal to 'canonical up to coherence'.

More generally a morphism from the free envelope that preserves universal cells but not literal chosen expressions can be strictified: restrict it to old presentation data and re-extend using target choices. The preceding recursive comparison gives an invertible transformation from the strictified morphism to the original strong one. Transformations are determined by old components by the same universal-factor argument. Consequently inclusion of strict choice-preserving interpretations into strong interpretations is fully faithful and essentially surjective. This is the asserted equivalence of categories in the unchosen/strong convention. It does not assert that arbitrary lax morphisms preserve universal cells.

## 8 The ordinary separating semantic equipment

Let G_N be the bare graph-cut multicategory, including its empty graph and all empty-block operations but no scalar labels. Define its UNNORMALIZED planar monoidal envelope explicitly.

An object is a finite WORD of ordered graphs of size at most N, including possibly empty graph entries. A morphism from (G1,...,Gr) to (H1,...,Hs) is a weak ordered allocation r=l1+...+ls together with, for each j, a graph-cut witness from the j-th contiguous run of source graphs to Hj. A zero-length run is allowed precisely when Hj is the empty graph. Composition is forest substitution with the actual occurrence allocation retained. Tensor concatenates words and forests. The category laws follow from the original graph substitution laws; the tensor interchange law is equality of the same disjoint ordered forests. The tensor unit is the EMPTY WORD, distinct from the one-entry word [empty graph].

Now define E_ord with vertical category B. A horizontal is a pair (L,S), where L is a graph word and S a finite span A<-S->B. A multicell is a graph-envelope morphism from the concatenation of source words to the target word, an endpoint-compatible map from the tuple-pullback composite source span to the output span, and ONE GLOBAL scalar m in M. It is not a pointwise family of scalar maps. Substitution is forest substitution, tuple span-map composition and multiplication of all participating scalar labels. Commutativity of M gives the required interchange/independent-slot composition laws.

Restrictions leave L unchanged and pull back S along the two boundary maps; their graph component is id_L and scalar is 1. The universal restriction inverse sends a map of source tuples into S to the uniquely forced endpoint-lifted tuple, retaining the same graph morphism and scalar. Thus restriction is cartesian in every arity.

The horizontal unit is (empty word, identity span A), with identity graph morphism and scalar 1. Its all-context factorization simply inserts or deletes the forced equal endpoint coordinate. Universal composition concatenates graph words and uses the tuple-pullback span composite; its universal cell has graph identity, span identity and scalar 1. Factoring is the graph tensor identity, the canonical reassociation of tuples, and the unchanged scalar. These are actual all-context bijections, so E_ord is a chosen ordinary equipment. No preexisting graph assembly has been made invertible by this construction.

For the virtual separating model use GraphSpanModel.md, whose horizontal graph part is a SINGLE graph rather than a word. Its universal units and restrictions were proved separately; it need not have all universal composites. Neither semantic model is asserted to be the free term envelope.

## 9 Full recovery of original semantic fibres

Map the original component (G,h:A->B) to ([G], graph-span(Fh)) in E_ord. For the virtual model use (G,graph-span(Fh)). Keep the entire original interface path as part of the comparison.

The tuple composite of graph spans of Fh1,...,Fhn has one tuple for each a in F(A0), with every later coordinate forced by the functions. Its left projection is a and its right projection is F(hn...h1)(a). A span map from this composite to graph-span(Fh) is therefore UNIQUE when F(hn...h1)=Fh and nonexistent otherwise. Faithfulness of F makes this exactly hn...h1=h. For the nullary case the source is the diagonal span; the same argument gives h=id, and the graph morphism from the empty word to [G] exists exactly when G is empty.

A graph-envelope morphism from the original one-entry words [G1],...,[Gn] to [G] is EXACTLY a single original ordered partition witness, including all empty entries. There is just one output root; no multi-output occurrence allocation is forgotten. The remaining cell datum is the single original scalar m. Thus every original full profile maps BIJECTIVELY to its semantic cell fibre, uniformly in N,K,M and all arities. This verifies full faithfulness of the semantic comparison on original profiles, not full faithfulness of the free-envelope unit.

Interpret V and O in their respective semantic models by Section 5. If two old cells have equal images in V or O, their images in the separating semantic model are equal; the preceding bijection implies equality of the old C5 cells. This proves old-profile equality conservation.

For unary graph-envelope isomorphisms between one-entry old words, the two graph maps must be the original unary identity cuts, so the graphs are equal. An isomorphism between graph spans of two old functions with the same endpoints forces those functions equal; then faithfulness of F forces the grades equal. Distinct old tagged interfaces have not been identified. Hence new unary globular isomorphisms in V or O cannot connect previously distinct old components. An old scalar m can become invertible in the envelope only if its semantic scalar is a unit of M, exactly its old invertibility condition.

An old semantic refinement arrow is an occurrence-indexed tuple of old cells with the indicated full profiles. Its image tuple is equal to another such image exactly when its entries are equal. The argument above reflects each equality. Composition is the original tuple substitution on both sides. Thus the old refinement subcategory is faithfully embedded with equality reflection; when the ambient semantic comparison is restricted to old input/output profiles for every tuple entry, its full fibre calculation gives the stronger corresponding full recovery. No assertion erases the tuple in favour of equality of composite endpoints.

## 10 Exact graph-word assembly boundary

For a graph-envelope morphism F from a word of length r to a word of length s, each input occurrence is assigned to exactly one output root, in order. This determines a monotone function [r]->[s], possibly missing output roots that have nullary cuts. The function of a composite is the composite function.

If F is invertible, its function and the inverse's function are mutually inverse monotone bijections. Therefore r=s and the allocation is the identity. Each output root then has exactly one input; the unary graph-cut rule forces equality of the corresponding ordered graphs and the identity graph witness. Conversely those identity forests are invertible. Thus the graph envelope has no other isomorphisms.

In particular an assembly from an r-entry word to a one-entry whole graph is invertible precisely when r=1 and the cut is the unary identity. Empty graph entries COUNT as occurrences. The nullary assembly []->[empty graph] is not invertible. Nor is [G,empty graph]->[G], even though it has a right inverse inserting the old nullary empty witness: the reverse composite allocates BOTH source occurrences to the first output root and generates the second output nullarily, whereas the identity forest assigns one source occurrence to EACH output root. Their occurrence functions differ.

This is intentionally distinct from the single-graph model's representability boundary, where a path with at most one nonempty graph can have an opcartesian composite. The free unnormalized envelope need not preserve that additional preexisting universal marking. Imposing such preservation is a separate relative-presentation problem, with the cartesian-marking no-go above illustrating why arbitrary markings cannot be added without analysis.

## Status and remaining limits

Independent review status is recorded in ScopeAndStatus.txt. The envelope theorem does not determine every new original-profile cell, prove a normal form for the whole equipment, establish arbitrary quotient saturation, or construct the mixed graph-geometric 2-Segal/module object. The concrete product-style separating equipment is baseline infrastructure. The bounded graph-dependent quotient and exact-cut/interface compatibility results are established separately in GraphDependent_Quotient_and_Cut_Memory.md and Global_Cut_Repair.md; the explicit enlarged local presentation is in Extended_Local_Presentation.md.
