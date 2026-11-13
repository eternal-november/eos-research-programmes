# Full occurrence-refinement coherence for the twisted comparison

Author derivation, 31 October 2026; independently generated presentation, not an acceptance declaration. This is the refinement companion to `twisted_normal_forms_draft.md`. It concerns the selected mixed-law comparison quotient, not the bare pushout. It supplies the full-refinement part of original I1 lines 622–637; cuts and interface descent require their separate hypotheses.

## 1. Exact calculus, syntax and category level

Fix arbitrary finite N,K,A,B and a table λ satisfying U, BAA and BBA of the coefficient companion. Let L=A⋈λB. Use the old graph calculus P with terminal old scalar. Its reduced old presentation has binary actual-cut generators c and designated empty/id nullaries u, with R, UL, UR of original C5. This removes only the old, definitionally identity d_1; it does not remove any graph/interface operation. Equivalently one may retain d_1 and its identity contraction, with the resulting redundant critical squares. Every whole graph, actual partition, full grade string, empty occurrence and repeated position is retained. The graph restriction conventions and canonical old right comb are exactly original C5 §§1–6. The pins and limits of imported results are recorded in I5 `model_and_core_comparison.md` §7. We do NOT import ordinary coherence for the newly added rules from old B3.

Adjoin unary A_a and B_b at every nonempty colour, including unit generators. At empty colours there are NO new coefficient generators. In addition to R,UL,UR orient:

* A_1(x)→x, B_1(x)→x;
* A_a A_c(x)→A_ac(x), B_b B_d(x)→B_bd(x);
* B_b A_a(x)→A_u B_v(x), where λ(b,a)=(u,v);
* X_q c(x,y)→c(X_q^left(x),X_q^right(y)), X=A or B.

Here X_q^child is X_q at a nonempty child colour and the identity at an empty child colour. Coefficient multiplication/sorting is followed by ordinary unit deletions when desired, not by an implicit new equation. Every old generator of nonempty output is such a binary c. There is no diagonal/nullary overlap: nullaries have empty output and cannot be children of X. All metavariables occur ONCE on each side; diagonal movement copies a finite coefficient label, not a frontier variable.

Define the semantic calculus independently as P[L], with active-input labels and substitution (l_i,m_ij)↦l_i m_ij; all old entries are retained. Define Ref(P[L],W) independently: objects are operations of output W; an arrow α→β is the ENTIRE tuple (γ_i) at the original ordered input occurrences of α, satisfying α[γ_i]=β. Each γ_i includes its own full frontier, actual partition, grades and active label array. Composition is (γ_i[δ_ij]) with the canonical occurrence split. This is not a category of endpoint equations or of root-to-final label totals.

We first construct Cλ with RAW term objects. Its comparison to Ref is an equivalence, NOT an isomorphism, since distinct raw bracketings remain distinct objects. The full subcategory Cλ,nf on irreducible terms has an actual category isomorphism to Ref. Alternatively a syntactically skeletal completion can be obtained using these normal representatives. This distinction is mandatory.

## 2. A genuinely terminating orientation

For any extended term t, let:

* D(t) be the sum, over all coefficient vertices, of the number of OLD structural vertices (c and u) strictly below that vertex;
* B(t) be its number of binary c vertices;
* A(t) be the sum over c vertices of the number of c vertices in their left subtree (ignore intervening unary coefficients);
* C(t) be its number of coefficient vertices;
* I(t) be the total number of B-before-A pairs in its maximal uninterrupted unary coefficient chains.

Order (D,B,A,C,I) lexicographically in N^5.

Diagonal movement strictly lowers D. Indeed, for X c(t_1,t_2), the removed X contribution is 1+old(t_1)+old(t_2); its newly copied vertices contribute the sum of old(t_j) over NONEMPTY child colours only. The drop is at least 1. Other coefficient vertices have unchanged old descendants; old vertices are neither copied nor moved across any other coefficient. C can increase, which is harmless.

R preserves D and B and strictly lowers A by 1+B(x) in c(c(x,y),z)→c(x,c(y,z)). Coefficients in x,y,z retain precisely their old descendants; coefficients above the redex retain its unchanged old vertex count. UL and UR never increase D and lower B. These claims hold in arbitrary contexts.

Unit deletion and same-channel multiplication never increase D, preserve B,A, and lower C. A sorting step preserves D,B,A,C: its two adjacent unary vertices have the same old descendants and merely exchange channel order; it lowers I by one. If sorting is implemented together with unit deletions, C decreases instead. Other inversion pairs on the same chain are unchanged by the adjacent swap. Thus every actual contextual step strictly lowers this tuple. This proof applies to arbitrary depths, arbitrary numbers of empty profile entries and repeated colours. It does not rely on a bounded search.

An irreducible term has no coefficient above an old node: following a coefficient chain downward otherwise reaches a diagonal redex. Its old skeleton has no old unit or association redex and hence is the unique old canonical right comb (or identity leaf, or designated nullary). At each nonempty external leaf its coefficient chain is either empty, a nonunit A, a nonunit B, or a nonunit A followed by a nonunit B. Empty external leaves remain literal leaves without labels. Thus irreducibles are in bijection with full semantic operations (α,((a_i,b_i))_active), including their entire profiles. Write N for this explicit constructor.

Every rule preserves P[L] evaluation: old rules preserve the retained data; diagonal copies the SAME factor to every active child; tables and sorting are precisely valid L equalities. Termination and the preceding irreducible classification prove that every reduction of t ends at the same N(ev(t)). This establishes object confluence without assuming a path-coherence conclusion.

## 3. Finite, explicit ordinary homotopy basis Oλ

Objects and equations below are syntactic. For each critical source choose the two positive joining words described here, and impose equality of those words. Apply these finite diagrams in all well-typed contexts and substitutions. Also impose disjoint-redex squares and variable-overlap squares (the inner equation is carried to the unique residual of its variable). Actual label tables and restrictions decide all typing.

1. **Old/old:** the R/UL/UR sublist of old B3: c(c(x,y),u); c(u,u); c(c(c(x,y),z),w); c(c(u,x),y); c(c(x,u),y). The joins are respectively the right-unit triangle, unit triangle, four-leaf pentagon, and left/right unit triangles. Use the actual joining words from old Completion Comparison rows 1,3,8,9,10, with all their cut labels. Coefficient-containing variable substitutions are allowed and unchanged.
2. **Coefficient/coefficient:** AAA and BBB associativity, BAA, BBA, all coefficient/unit overlaps (including mixed units). The two branches multiply/sort to their identical A-then-B pair using U, BAA, BBA. These are exactly the finite word overlaps of the companion theorem; the row labels and endpoints are actual table values, not new symbolic associativity equations.
3. **Multiplication/diagonal:** X_p X_q c. First multiply and distribute. Alternatively distribute the inner X_q, then the outer X_p, then multiply at EVERY active child. Both end at c((X_pq)^left,(X_pq)^right) with the original variable subtrees. Unit values are deleted by fixed unit paths on both sides if needed.
4. **Unit/diagonal:** X_1 c. First delete X_1; alternatively distribute and delete all active child X_1's. Both end at c(x,y).
5. **Sorting/diagonal:** B_b A_a c. Sort first using the single pair (u,v)=λ(b,a), then distribute both letters. Alternatively distribute A_a and B_b and sort at EVERY active child using that SAME (u,v). Both end at c((A_u B_v)^left,(A_u B_v)^right). Empty children receive identity on both routes. The order of independent child steps is fixed, say left then right; other orders are covered by disjoint squares.
6. **Diagonal/old:** X_q l where l→r is each of R, UL, UR with nonempty output. First apply the old rule under X_q, then distribute X_q through all old nodes of r. Alternatively distribute through all old nodes of l, then apply the old rule with X_q appended to EACH nonempty template variable, and identity at each empty template variable. Both end at r with that identical decorated template frontier. For R this is the distribution/association cube: X reaches x,y,z, not merely one selected leaf. For UL/UR the removed u has empty output and never receives X. The old rule at the end is one actual contextual instance, not an appeal to semantic equality.

This list exhausts nonvariable critical overlaps. The possible nonvariable heads of left sides are c in R's left child, u in an old unit child, a coefficient in a table/sort child, and c immediately beneath a diagonal coefficient. Two old rules give item 1; two coefficient-word rules give item 2; coefficient-word with diagonal gives items 3–5; diagonal with an old rule gives item 6. Distinct diagonal rules cannot overlap nonvariably: X c has only the old c as its nonvariable proper subterm, while another diagonal requires coefficient head. No coefficient rule is typable over the empty-output u. All remaining overlaps lie at disjoint positions or inside a variable and have the specified residual squares. Every variable occurs once, so no variable-overlap requires deletion or duplication of a rewrite path.

The description is a finite context-schema basis for fixed N,K,A,B: finitely many colours, old generators, coefficient labels, rule templates and critical overlaps. Arbitrary contexts/substitutions remain unbounded. An independent implementation can enumerate typed nonvariable unifiers of these finite left sides and compare them with this classification. Deterministic positive normalization of each finite critical endpoint is also a terminating way to generate equivalent longer joining words, but semantic-kernel equality is not a defining relation.

**Ordinary coherence proof.** Choose deterministic positive normalization ν_t:t→N(ev(t)). Well-founded induction on the actual measure of §2 proves every two positive normalization paths equal modulo Oλ. Compare their first steps; the classification supplies a joining diagram e;p=f;q. Append normalization of the join. At each first reduct the induction hypothesis identifies its original tail with the chosen joining tail followed by normalization. Hence the two paths agree. The identical-first-step case is immediate. Consequently ν_t=e;ν_u for every positive edge e:t→u, and inverse cancellation proves that every equation zigzag t→u equals

    κ(t,u)=ν_t;(ν_u)^−1.

This holds iff the normal objects agree. We are explicitly taking the quotient of the free equation track category by THESE chosen critical homotopies, not asserting literal equality of all rewrite proofs before quotient, or invoking object confluence as path coherence.

## 4. Independently generated equation/graft completion

Take all raw extended terms of a fixed whole W as objects. Edges are:

* insertion of one primitive corolla (old or coefficient) at an ACTUAL external leaf;
* an oriented contextual equation occurrence with its rule/address/substitution data;
* a formal inverse for each such equation occurrence.

Take the free category and quotient by the following independently declared relations:

**Rcat:** equation inverse cancellations; raw graft identities and interchange of adjacent incomparable insertions. Thus an actual forest F determines R(T,F):T→T[F], independently of its elementary execution order, and R(T,F);R(T[F],H)=R(T,F⋆H). This is equality of the same raw forest, not equality of evaluation.

**Oλ:** precisely §3's ordinary homotopies.

**MOut:** for each rule occurrence e:T→U and elementary graft G at their common ordered frontier,

    e;R(U,G)=R(T,G);e[G].

The residual e[G] is the same rule with those variable subterms extended; it exists because the full frontier is preserved occurrence by occurrence.

**MIn:** for each BARE identity-leaf template l→r among ALL old and new rules, each ambient T and matching external occurrence i,

    R(T,i:l);T[e]_i=R(T,i:r).

In particular this includes bare coefficient table, unit, diagonal AND mixed sorting templates. It does not initially assert this for arbitrary substituted forests or all semantically equal entries. There are finitely many bare labelled templates. MOut uses arbitrary syntactic occurrences but one primitive graft; its occurrences are effective context/substitution schemas. Nothing in this category definition mentions Ref, evaluation, semantic kernel or equality of parallel paths.

## 5. Derived full graft naturality and path normal forms

MOut extends to any forest by induction over its finite primitive-graft execution, using Rcat. It extends to inverse equations by cancellation and to equation words by concatenation:

    z;R(U,F)=R(T,F);z[F].

Here the frontier matching is ordered occurrence matching, never matching by equal component type. Empty/nullary insertions remove the corresponding occurrence on both sides.

MIn extends to one equation in an arbitrary forest entry as follows. If that entry changes C[l[σ]]→C[r[σ]], first graft the forest F0 with the distinguished redex replaced by one identity leaf. Next graft bare l at that specific new leaf, and then σ at its template frontier. On the alternative path graft bare r and the same σ. Move the bare equation across σ using the already proved MOut extension, apply bare MIn, and use Rcat to reassemble. Therefore

    R(T,F);z=R(T,F')

for that contextual substituted entry equation. This factorization uses one actual distinguished hole, even among repeated colours. No variable is copied by diagonal, so the same σ is legal on both sides. Extend by inverses, concatenation and finite iteration over original entries. Ordinary coherence makes the resulting whole-tree equation path independent of all choices.

Now induct on a mixed generator word p:T→U. It factors as R(T,F);z with z a pure equation path. Appending an equation extends z. Appending a graft G moves z past G by MOut and composes forests by Rcat. Hence

    p=R(T,F);κ(T[F],U).

Normalize EACH original forest entry separately, obtaining F↓. The derived MIn gives R(T,F);κ(T[F],T[F↓])=R(T,F↓); ordinary coherence then yields the canonical representative

    p=R(T,F↓);ν_(T[F↓]);(ν_U)^−1.                 (★)

This is not normalization of only the whole composite. Every F_i↓ retains its output component, own ordered frontier and length, actual partition, intermediate grades and its own active A×B coefficient array. Equation edges can change source syntax but not the ordered frontier used in this induction.

## 6. Full comparison and independently constructed inverse

Map raw objects T to ev(T). Map a graft to its full tuple of primitive evaluations at the specified occurrence and identities elsewhere; map an equation to the identity tuple between equal evaluated objects. Every defining relation is sound: Rcat is forest composition/interchange; Oλ and cancellations map to identities; MOut maps to the SAME ordered graft tuple; MIn compares ev(l)=ev(r) in the changed entry, not just total outer composites. Thus this defines Pλ:Cλ→Ref(P[L],W).

For fixed raw endpoints T,U and an independently given semantic arrow γ=(γ_i):ev(T)→ev(U), put F_i=N(γ_i). The endpoint equation and operation completeness imply T[F] and U have the same normal object. Set

    H_T,U(γ)=R(T,F);κ(T[F],U).

Then PλH(γ)=γ entrywise. Conversely (★) gives HPλ(p)=p. Therefore, for arbitrary mixed paths p,q at fixed endpoints,

    p=q  iff  (F_i↓)_i=(G_i↓)_i
         iff  Pλ(p)=Pλ(q) as FULL refinement tuples.

This is proved full faithfulness, not equality defined as a semantic kernel. Composition of H follows by substituting forests and normalizing each entry: N(γ_i)[N(δ_ij)] normalizes to N(γ_i[δ_ij]), with the identical ordered descendant split and correlated multiplication in L. Identities are immediate. Every semantic object has representative N(α). Consequently Pλ is an equivalence with section on normal objects, and its restriction Cλ,nf→Ref(P[L],W) is an actual isomorphism. The natural isomorphism from raw objects to the section is ν_T; its naturality follows from the established hom theorem.

All choices are now proved irrelevant: primitive execution orders by Rcat; ordinary reduction paths by §3; equation/graft commuting choices and choices of entrywise reductions by MOut, derived MIn and (★). No relation identifies arbitrary parallel mixed arrows: different full normal forests remain distinct, even with identical endpoints.

An effective equality algorithm validates a finite word, maintains one raw forest entry per ORIGINAL source leaf, leaves this forest unchanged on equation edges, and updates the unique descendant position on graft edges using the full ordered entry profiles. It normalizes every resulting entry by §2 and compares the complete arrays. This works for unbounded profiles/history/depth and produces derivations by the preceding induction; finiteness of the palette does not mean finiteness of the category.

## 7. Exact transfer criterion and local-theory comparisons

Construct the same completion for P[A], P[B], and P using their corresponding subsets of rules. The same proof, with the absent channel deleted, gives their independent full-forest comparisons. Sending local primitive edges to global edges induces functors: local ordinary diagrams may be taken as the same global diagrams; their MOut/MIn and Rcat are included literally. On normal semantic entries these maps are

    (α,(a_j)) ↦ (α,((a_j,1))_j),
    (α,(b_j)) ↦ (α,((1,b_j))_j),
    α ↦ (α,((1,1))_j).

The diagrams with Pλ and the independently defined Ref of these calculus inclusions commute on actual generators and on each full tuple. Both local functors are faithful, since the pair injections are injective. They reflect equality of local paths at matching endpoints. The common-image intersection consists precisely of the old P data, entrywise, because (a,1)=(1,b) forces a=b=1. This includes nontrivial old operations and interface paths, not merely units.

**Certificate transfer criterion.** Fix and explicitly identify the source and target operations, old retained whole/profile data and original occurrence indexing. Two candidate refinement certificates, possibly from different local descriptions, determine the same global certificate IF AND ONLY IF their full normalized entry families have identical old partitions/frontiers/grades AND identical coefficient pair at EVERY active frontier position of EVERY entry. A candidate global certificate has an A-local representative iff its endpoints are A-local and every normalized entry is A-pure, i.e. all its B coordinates are 1; the analogous B statement exchanges channels. Sufficiency constructs every local entry from its local normal form and uses (★); necessity is injectivity and the full semantic tuple definition. For an unnormalized description compute the pair coordinates using λ, not by forgetting mixed factors independently.

This is a literal-path/full-tuple certificate criterion. It does not assert independent local class matches glue, nor multiplicity or repair-optimum preservation. More precisely, A inclusion IS full on these normalized Ref arrows: (a,1)(c,d)=(ac,d), so an A-pure target forces d=1 at every active entry frontier. B inclusion need not be full for a general λ: let A=C_2, B={1,z} with z²=z, and use the semidirect law where α_z sends every element of A to 1. The B-pure unary source (1,z) has a global refinement entry (a,1), a≠1, ending at the same B-pure unary target (1,z). That entry is not B-pure, so the arrow has no local B representative. When all α_b are automorphisms (in particular the cyclic inversion positive family), α_b(c)=1 forces c=1, so B inclusion too is full on Ref arrows. Foreign inverse factors inside one entry disappear in its operation normal form and therefore are NOT counterexamples to Ref fullness; they DO obstruct fullness of the richer marked cut records. These are distinct claims. Cut fullness and noninvertible interface reflection remain separate tasks.

### Finite-monoid corollary for the actual bare pushout

For ANY finite monoid M, delete the B channel (equivalently take B terminal and remove its definitionally identity unary symbols). Sections 1–6 give an independently generated completion C_M with full normal-object isomorphism C_M,nf≅Ref(P[M]). Its finite critical basis is old/old, MMM associativity/unit, multiplication/diagonal, unit/diagonal, diagonal/old, disjoint and variable squares; MIn and MOut include every remaining rule. Thus this theorem is not restricted to matched products.

A monoid homomorphism h:M→M' maps D_m to D_h(m), fixes old syntax, maps grafts to the corresponding grafts and equations to the corresponding equations (or their identity normalization). Its images of ordinary diagrams are parallel pure equation paths and hence agree by the ALREADY PROVED ordinary coherence of C_M'. Rcat and MOut are preserved syntactically; MIn maps to its target counterpart, with ordinary coherence absorbing any chosen unit normalizations. This defines a functor C_M→C_M', commuting with the independent full-tuple semantic maps. On normal-object completions include target normalization; functoriality follows from the full hom comparison, and its action is exactly entrywise h on every active frontier coefficient. If h is injective, this functor is faithful and reflects equality of full local certificates; no general fullness assertion follows.

Apply this to the independently proved finite bare monoid pushout Q_J=A_m⊔_C B in `interface_pushout_theorem_draft.md`. All four finite coefficient theories P[A_m],P[B],P[C],P[Q_J] have the SAME type of independently generated full path comparison. In the repaired J=∅ case both input homomorphisms are injective, so both presented local refinement completions embed faithfully on full normal tuples, over their literal common C records. For J≠∅ the actual coefficient collapse identifies unary entries already at a nonempty identity profile and consequently identifies the corresponding refinement certificates. Thus the bare-pushout positive/negative family inherits this full path theorem, rather than relying on the separate λ operation-normal-form argument. Its universal property as a graph-calculus pushout still requires the companion's under-P universal-property proof; it is not inferred merely from the finite-monoid corollary. Here C_Q_J denotes the completion of the FULL Q_J multiplication-table presentation, not a claim of coherence for the raw union of the input equation paths. Local generators and equations map to their image table/diagonal relations and fixed unit normalizations in that chosen output; target ordinary coherence and MOut/MIn validate the local certificate maps. Operation-level equality between the raw union and this presentation is supplied by the one-dimensional pushout theorem. No path-category equivalence for an uncompleted raw union, or two-dimensional pushout property, is inferred. Proving such a stronger statement would additionally require chosen derived mixed-rule paths and defining higher cells, which are outside this claim.

In the repaired partial-map pushout Q_∅=M, nonfullness of the local A_m refinement inclusion can be witnessed by an ACTUAL foreign normalized entry, not hidden chronology: take unary local source c and local target p=y_∅; the global entry u satisfies cu=p, while cA_m⊆{0,c}, so no local entry has that endpoint equation. For the B inclusion, take local source and target u; every y_S satisfies u y_S=u. If S≠∅, the global entry y_S is not in B, and differs from the local entry p although both yield the same target. At any nonempty identity graph profile these are literal full refinement tuples. These examples show that faithful input embeddings in the repaired bare pushout need not be full refinement functors, independently of the semidirect class where fullness can hold.

### Marked cut histories are a different retained object

A refinement arrow retains its original-slot factor operations, not every intermediate factor of an arbitrary execution history. If a certificate additionally marks a finite cut tree with individual factor vertices, apply the operation/entry normalizer SEPARATELY within each marked factor and retain the entire ordered marked tree, its incidences, colours and every normalized vertex array. No equation movement may cross a marked boundary unless the certificate explicitly includes the corresponding contraction/expansion move as data. Equality of flattened Ref arrows is therefore not an equality criterion for these richer cut records. For a fixed marked skeleton the same entrywise calculus bijection gives a bijection on labelled marked records; admissibility is checked at every vertex by the local substitution equation. This is exactly the level used by the separate joint-cut theorem and its accumulated-prefix formulas. It prevents a factor label and its inverse on successive edges from disappearing merely because their total is the identity.

## 8. Sharp controls: why every layer matters

**Object confluence without Oλ is insufficient.** A critical loop consisting of one reduction branch followed by the inverse of the other remains a formal equation loop until the stated homotopy is imposed. Our theorem is about the specified quotient, not all rewrite 2-cells in an unquotiented track category.

**Deleting MIn breaks full faithfulness.** Retain Rcat, all Oλ, all MOut, and equation inverses, but remove MIn. Assign integer weight 1 to every primitive graft and 0 to every equation (and its inverse). Every retained relation preserves total weight: Rcat merely reorders the same insertions, Oλ uses only equations, and MOut has the same single graft on both sides. At a nonempty identity leaf x, let p be graft A_1 then its deletion equation back to x; let q=id_x. Their semantic refinement tuples are both the identity, but weights 1 and 0 prove p≠q. This is a precise negative model for the missing-inner-relation error. The bare A_1 MIn imposes exactly this missing equality. Similarly each omitted schema must be checked rather than inferred from object confluence; this example proves necessity of INNER compatibility as a family, not independence of every individual bare instance.

**Deleting ONLY mixed-sorting MIn also fails.** In the positive inversion example A=C_3=⟨a⟩, B=C_2=⟨s⟩, retain ALL relations above except the bare MIn instances for B_b A_a→A_u B_v. Give an A_(a^j) graft at graph H weight |V(H)|j in Z/3, every other primitive graft weight 0, and every equation edge/inverse weight 0. Rcat, Oλ and MOut preserve weight. Every retained MIn does too: A multiplication is exponent addition, units have weight zero, B multiplication contributes zero, old rules contain no coefficient grafts, and diagonal preserves weight because the actual child partition satisfies |V(H)|=Σ|V(H_i)| (empty children contribute zero). Thus this is a well-defined additive invariant of the weaker presented category. At a one-vertex identity leaf, compare p = graft B_s A_a followed by its mixed sorting equation with q = graft A_(a^2) B_s. Both end at the SAME raw term and have the same full semantic unary tuple, but their weights are 1 and 2. Hence p≠q. Their equality is precisely the omitted mixed MIn instance. This verifies the new mixed inner law is not derivable even from all ordinary critical homotopies, all MOut, and all other inner laws. It is a sharper control than deleting the entire MIn family.

**Endpoint equality is insufficient even in the positive model.** Take A=C_3 and an old source operation α with two consecutive empty/id occurrences alongside a nonempty occurrence (profiles are unbounded). Refining the first empty occurrence by u and leaving the second an identity, or vice versa, gives the same final old operation/profile but different original-slot tuples (u,id) and (id,u). Both arrows have the same endpoints and every active label can be unit, yet the retained tuple criterion distinguishes them. No root-to-final coefficient aggregate can recover this distinction. Repeated nonempty component positions likewise must never be matched by type alone: original C5's six-vertex example separates refinements of its equal middle components by actual partition and occurrence index.

**Different label entries with the same entire endpoint operation.** In the permitted positive commuting case A={1,0} with absorbing 0 and B=C_2, fix a nonempty one-vertex colour and the raw source T=A_0(x). One arrow is id_T, with normal entry the unit identity; another grafts A_0 at its original leaf and applies A_0 A_0→A_0, returning to the SAME raw endpoint T. Their full normal entry labels are (1,1) and (0,1), so they are distinct by §6, whereas their final root-to-leaf product is (0,1) in both cases. This is a direct parallel-arrow negative control for discarding entry labels in favour of even the complete final composite. It is not merely a comparison of arrows with different targets.

**Mixed coefficient necessity.** Failure of U, BAA or BBA identifies two distinct claimed A×B normal pairs. Thus no comparison with the stated pair-labelled semantic refinement category can exist: already the unary nonempty profile violates operation bijectivity. This is the exact converse for this finite-table normal-form target, not a claim that every failed table necessarily collapses both pure local theories.

## 9. Scope and baseline

The new proof above supplies an actual lexicographic termination argument, complete finite ordinary critical basis with correlated diagonal cubes, independently generated equation/graft relations, and full original-entry forest comparison. Old B3 supplies the template for the mixed-normalization argument but not its new coefficient critical basis. Ordinary coherent rewriting supplies the homotopical method; it does not by itself identify this occurrence-sensitive refinement completion. Structured/decorated cospan constructions supply composition frameworks, not the specific entrywise certificate criterion or joint-cut reflection. No novelty for matched products, critical-peak induction or free-category presentations is claimed. Independent mathematical audit and finite all-shape checks remain required before I1 acceptance.
