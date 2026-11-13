# Independent adversarial review: actual C5 kernel criterion and envelope bridge

29 October 2026. Independent AI proof review, not Lean verification, human review, or a novelty assessment.

## Verdict

**The original-calculus classification and the conservative envelope quotient bridge pass this review within their stated scopes.** No counterexample or proof-breaking gap was found. They do not complete the full original-to-extended presentation comparison, classify all new envelope cells, or make arbitrary noninvertible cut comparisons invertible.

Two precision edits were requested in the concrete-extension paragraph: retain every shared substitution boundary map, including the lone map for a nullary outer operation; and distinguish equations indexed by every concrete nonempty horizontal from equations indexed only by original components. The author applied these edits and they were reread. Neither changes the proof.

The strongest new conclusion is not a new general scalar mechanism. It is the source-level restriction: universal lifting at specified original endpoints forbids partition collapse, reduces graph-indexed scalar forgetting to a uniform unit-subgroup action, and permits exactly that old kernel to survive the free equipment constructors without additional old equalities.

## Sources actually checked

* `main/C5_Fixed_Endpoint_Kernel_Classification.md`.
* `audit/Original_Presentation_Inventory.md`.
* Original `research/workstream_A/rewrite/A3_LOCAL_COMPARISON.md`, especially §§1–6: actual generators, seven relations, full operation profiles, nullaries, substitution, and presentation/flat-operation comparison.
* Existing `structural_extracted/GraphSpanModel.md`, particularly its cell and substitution definitions and cartesian/contextual-unit formulas.
* New `main/Original_Envelope_Quotient_Bridge.md`.
* New `main/Generation_Boundary.md` and `main/KernelPair_Provenance_Repair.md` for consistency and boundary checks. The generation theorem was checked against the graph-word isomorphism proof in the existing envelope source; the repaired groupoid theorem was checked directly, with a successive-change clarification requested below.

## 1. Partition obstruction

Proposition 1 is correct for **parallel** congruences and fixed original outer witnesses, target witnesses, and replacement profiles. The identity-profile forest does not allow reassignment of vertices between outer slots: each replacement has one leaf and therefore its only graph block is the entire original child graph. Scalars can change; the outer ordered partition cannot.

The smallest illustrative obstruction uses a two-vertex edgeless whole with two singleton input components. The ordered partitions `({0},{1})` and `({1},{0})` have identical component profiles but are different actual operations. Identifying them creates a quotient identity-forest arrow without an actual lift between these specified representatives. Repeated equal components do not invalidate the argument, since slots are occurrence-indexed.

This is not a prohibition on every quotient or on moving the outer representative. Changing that lifting requirement changes the result.

## 2. Scalar congruences and exact classification

Lemma 2 correctly uses the actual binary generator with identity interface grades to propagate the kernel of any induced subgraph to the whole. Those identity-grade instances exist at any object of the assumed nonempty K. Unary operations give monoid compatibility. Full flat substitution establishes sufficiency, including empty blocks and arbitrary arity.

Theorem 3 has no hidden cancellation assumption:

1. A nullary original outer operation at `(empty,id_A)` has no inner cell whose scalar could be changed. FL therefore forces scalar equality at the empty graph. Although other empty-graph components need not admit nullaries, graph-indexing makes this equality apply to their scalar relations too.
2. For `h` in the singleton-graph class of 1, lifting the identity child under outer scalar `h` to target scalar 1 produces `k` in the same class with `hk=1`. Commutativity makes this a two-sided inverse. No finiteness or cancellativity is needed.
3. Partitioning any nonempty ordered graph into all its actual singleton vertices is an available original operation, including when the whole has cross-edges. Lifting its identity forest forces every class to lie in the corresponding orbit under the singleton subgroup.
4. Induced-subgraph inclusion gives the converse containment. Thus the same subgroup acts on all nonempty graphs.
5. Sufficiency adjusts one child with a nonempty graph. Such a child exists whenever the whole is nonempty; it cannot be a nullary operation. The modification changes no partition, interface arrow, or replacement profile. If the whole is empty, all relevant scalar classes are exact and no adjustment is needed.

The assumptions `N>=1`, nonempty K, and graph-only scalar indexing matter. For `N=0` or empty K, the subgroup need not be determined; for profile-dependent kernels, the theorem is not a classification. These cases are not claimed.

The added equations are generated by actual original D operations. DA combines decorations; DL/DR transport them through old binary cuts; the previously proved full flat normal form accounts for all profiles. The explicit scalar relation is a separating model, so contextual use cannot secretly collapse empty scalars. This is not a semantic-kernel definition disguised as a presentation proof.

## 3. Concrete span extension versus free envelope

The concrete-extension argument is valid because the relation retains the entire coefficient map. Equality of quotient composites already says that their composed coefficient maps agree. Scalar adjustment is not being used to solve an unproved coefficient-lifting problem.

Cartesian factorization sends the coefficient map to `(h*pi_0,phi,k*pi_n)`, retaining graph and scalar; its inverse selects the middle coordinate. Contextual unit factorization is also a bijection retaining scalar and output graph. Both directions preserve the relation, including nonsurjective and noninjective boundary maps and nullary source paths.

A nullary substitution still has its shared vertical map. This is why the full boundary-map skeleton must remain fixed when stating the extension of FL. A nullary forest is not an absent boundary.

Generation in the *larger concrete signature* by decorations on every concrete nonempty horizontal does **not** imply those decorations or all those horizontals are generated from original C5. The main theorem's explicit separation of these claims is essential.

## 4. New free-envelope quotient bridge

The separate bridge avoids that mistake successfully.

Completion commuting with added presentation equations follows from the same raw grammar and the same least congruence, provided closure includes L, U and, in the ordinary case, Q. This is stronger than closure under substitution alone. The inverse-factor equations then still exhibit universal bijections after quotienting.

The nontrivial conservativity step uses a separate model. In the ordinary graph-word/span model, total vertex number is conserved by graph-forest cells and additive on words. Hence a positive-grade child can occur only under a positive-grade output. Quotienting scalars by H-orbits at positive output grade and retaining them exactly at grade zero is therefore stable under every substitution. Restriction, contextual unit, and composite factorization retain output grade and scalar and act by bijections on the retained structural data, so their inverses respect the relation as well.

On original profiles, the graph forest to a one-letter output is the original actual partition, and the graph-span coefficient is forced by endpoint equations and faithful interface realization. Consequently this model reflects precisely Q_H on old cells. It proves the required absence of new old equalities in both V and O without any fullness or scalar normal-form assertion for new envelope cells.

The refinement paragraph is correctly limited to supplied tuples of old cells. It does not identify every newly available envelope refinement with an old one.

## 5. Generation obstruction and changed repair doctrine

The horizontal-generation obstruction is consistent with the preceding bridge. A singleton graph word forces exactly one old horizontal leaf, even when that graph is empty. Noninjective restriction can enlarge apex cardinality, but cannot increase the support relation's rectangle-cover rank. Nor can composition on either side with arbitrary relations. Thus the bounded original interface rank cannot generate arbitrarily large identity-span carriers with that graph word. The stated carrier schema supplies horizontal objects, not full cell generation or equality completeness.

The kernel-pair appendix explicitly changes discrete interfaces to groupoids and strict seam matching to weak matching. Its nullary diagonal is an equivalence in that changed setting, not a bijection in the original span model. The distinction is maintained. Its coherent-record construction must not be reported as the original seven-rule generation theorem or as a repair of missing old interface values.

## 6. Reproducible independent finite checks

Reran the author's `tests/check_c5_scalar_classification.py` successfully: 499 ordered-partition regressions plus the displayed cyclic, semilattice and absorbing-zero examples.

Added an independently written checker, importing none of the author's checking code:

    python tests/review_all_small_monoids.py

Saved output: `tests/review_all_small_monoids.json`.

It enumerates every labelled commutative monoid with identity labelled 0 through order four, every equivalence relation, and every monoid congruence. Counts:

| Size | Monoids | Congruences | Unary FL congruences |
|---|---:|---:|---:|
| 1 | 1 | 1 | 1 |
| 2 | 2 | 4 | 3 |
| 3 | 9 | 30 | 12 |
| 4 | 94 | 542 | 131 |

All 577 congruences satisfy the claimed equivalence between the unary class-image condition and unit-subgroup orbit classes. A further 243 hereditary graph-indexed congruence families on the empty graph, singleton, edgeless two-vertex graph and edge graph were checked through monoid order three. Explicit nullary, unary and every binary partition shape agree exactly with the predicted uniform positive-graph subgroup/equality-empty classification. These checks cover noncancellative monoids and absorbing elements as well as groups.

These bounded checks are regression evidence. The unbounded claim rests on the proof above, not these enumerations. No Lean formalization or theorem-novelty conclusion is supplied by this review.

## 7. Separate full review: horizontal generation boundary

**Verdict: pass.** In the cited source, a graph-forest morphism induces a monotone allocation of source occurrences to target occurrences. If forests are inverse, those allocation maps are inverse monotone bijections; consequently each is the identity and each corresponding graph is unchanged. This argument counts empty-graph occurrences: an empty graph is a letter, not the empty word. A nullary old assembly does not produce an inverse deleting that letter.

The new grammar induction then follows the unique old leaf of a singleton-word expression. Fresh units and every empty-word branch may have arbitrarily large spans; they still occur only before or after the unique graph-bearing span in a composite. If a relation is a union of k rectangles, its inverse image under arbitrary independent boundary functions is a union of at most k rectangles. Relational composition on the left and right sends each rectangle to another rectangle. No injectivity, surjectivity, or bound on those other spans is needed. Thus witness duplication cannot defeat the bottleneck. The diagonal's rank is its cardinality because a rectangle containing two diagonal pairs would also contain forbidden off-diagonal pairs.

The carrier repair is correctly typed: `I_A[id,l]` has span `A <- E -> E`, and `I_B[r,id]` has span `E <- E -> B`. Placing the new `D_G(E)` between them gives the desired one-graph span. Longer graph words follow by additional identity carriers at B; the empty word needs only the companion/conjoint composite. This proves semantic horizontal essential surjectivity of that enlarged grammar, not generation of maps or any cell normal form. It is one sufficient extension, not a minimality theorem.

Reran its checker: 4,096 composition triples, 256 restriction cases, and exact diagonal ranks 0 through 4 all passed.

## 8. Separate full review: kernel-pair provenance repair

**Verdict: pass in the explicitly changed groupoid/provenance doctrine, after the successive-change clarification below was applied and verified.**

For a fixed old span witness, every lift tuple has a unique morphism to every other lift tuple over that same witness, and none to a lift of a different old witness. Weak seam pullback contributes a unique connector exactly when old middle values match. Hence the fibre over a complete old feasible tuple is empty or contractible. Its nonemptiness is precisely the conjunction of image-membership requirements, with external endpoints included when not fixed. This proves full faithfulness and the claimed essential image directly; surjectivity of all interface maps guarantees coverage, but arbitrary maps do not.

For nullaries, the diagonal from K_f to the reindexed identity groupoid is fully faithful and essentially surjective because `(x,y)` with equal f-images is isomorphic to `(x,x)`. This is an equivalence over endpoints in the weak/homotopy sense, not a strict fibrewise set bijection. The empty-interface case is vacuous on both sides. Coverage of the old base still needs surjectivity.

The finite-tree statement is valid for the stated **complete provenance records**. Old witnesses, coefficient data, occurrences, graph partitions, old boundary values and the individual supplied refinement scalars are fixed labels of morphisms. Cutting and regluing these records retains their common data. Contraction/evaluation can forget a scalar vector and is not asserted faithful. It would be incorrect to transfer the fibre statement to a root-only record after dropping hidden intermediate old values, or to infer unnormalized cut equivalences from arbitrary scalar-bearing grafts. The file explicitly avoids both moves.

**Successive-change issue found.** For `B'' --g--> B' --f--> B`, the strict two-stage record `(z,x=g(z))` must have an arrow to `(z',x'=g(z'))` exactly when `f(x)=f(x')`, fixing all other old data. It must not require `g(z)=g(z')`. Equivalently the second stage is provenance-aware pullback over the first groupoid, not an independently constructed K_g over a newly discrete B'. With this definition, forgetting x is fully faithful and essentially surjective onto K_(fg); the weak variant allows extra x with `f(x)=f(g(z))` and has contractible fibres. Triple-change coherence then forgets the same coordinates.

A concrete counterexample to the incorrect iteration is constant `f:{0,1}->{*}` and identity g: K_g is discrete with two components, whereas K_(fg) is connected. This clarification was sent to the author and parent, then applied and reread. The file now gives the strict and weak arrow rules explicitly and extends them to arbitrary finite chains.

Reran the author's updated 15,009 finite checks successfully, including successive-chain arrows and joint scalar/boundary actions. Added `tests/review_groupoid_boundaries.py` and its JSON result: 3,030 strict-stage hom-pair checks, 13,752 weak-stage hom-pair checks, and 104 nullary endpoint-pair checks, plus the explicit negative control above. These tests verify the provenance-aware construction, not the incorrect independent K_g iteration.

## 9. Separate review: original scalar-cut memory

**Verdict: pass after the graft-domain correction and both empty-root wording qualifications were applied and verified.**

A fixed old tree and nonscalar partition/grade skeleton has precisely one scalar per internal semantic vertex. Nonroot positive labels in the normalized quotient class are units in H; nonroot empty labels are exactly 1. Therefore the actual aggregate equation determines the root scalar as m times the inverse product of those units, even when m is absorbing or otherwise noncancellative. This gives H^r actual objects. If the outermost factor itself is fixed to m, the allowed product is the stabilizer of m, not necessarily 1.

The edge-gauge formula is the actual naturality square of original unary D(g) maps: postdecorating the source node is equal to predecorating the target node's children. DA, DL and DR prove it, with the original R relation handling arity/bracketing. Bottom-up solution of the gauge equations gives a unique arrow between any two marked factorizations. No cancellation of the root m is used. In particular retaining marks eliminates stabilizer ambiguity even with a nonunit root.

Contracting an edge multiplies its child label into its parent; its gauge cancels from the adjacent formulas. For normalized expansion, the inserted edge gauge must equal the product of the gauges of its moved internal children, not simply 1. The proposed formula does exactly this. Contraction after expansion is identity, while the other composite has the unique natural isomorphism supplied by the actual connected thin gauge groupoid. Coherence is thus groupoid-valued, not equality of all marking sets or literal rotation outputs.

**Graft error found and repaired.** Arbitrary actual factorizations of an H-valued label need not have H-valued factors: in additive C4 with H={0,2}, 0=1+3. The final graft claim is now restricted to actual lifts of the replaced operation's normalized quotient factorization, with positive nonroot factors in H and zero-grade nonroot factors 1. That domain is closed under the stated grafts and the proof then works. It must not be broadened to all actual scalar factorizations.

**Empty-root precision.** Statements that empty/zero-grade vertices have scalar1 must say nonroot vertices. A zero-grade overall root retains the supplied m, including a decorated nullary m≠1. The displayed formulas already implement this, but two sentences in §§3–4 needed qualification; the author applied both qualifications and they were reread. This does not alter either theorem.

The combined kernel-pair/scalar record is a product only after fixing the nonscalar old skeleton and root m, not after declaring all local scalar labels fixed. Boundary arrows change lift names; scalar gauges change labels. They commute because neither formula depends on the other's coordinates. The kernel-pair appendix's edge marks are cumulative subtree products of the scalar-memory file's node labels; these are different coordinates on the same H^r, not different constructions. No coefficient exactness follows merely from scalar contractibility.

Independent checker `tests/review_scalar_tree_gauges.py` passes 6,191 scalar-tree assignments through five vertices for cyclic groups of orders two and three with absorbing nonunit roots. It checks bottom-up gauge reconstruction, root aggregate preservation and the C4 proper-subgroup graft negative control. Reran the author's checker: 921 tree/grade/root cases, 36,120 gauge arrows and 142,218 contraction equations pass. These are scalar-sector checks, not tests of free-envelope cell generation or noninvertible coefficient exactness.

## 10. Strengthened exact ordinary horizontal-image theorem

**Verdict: PASS.** The revised Generation_Boundary §4 proves more than the initial Boolean-rank obstruction: a semantic horizontal (L,S) is in the essential image of the original ordinary envelope exactly when L is empty or the nonnegative INTEGER factorization rank of the witness-multiplicity matrix of S is at most b.

Necessity does not require a singleton graph word. Choose any old horizontal leaf of a nonempty-word expression. Its multiplicity matrix factors through its actual apex, of size at most b. At every restriction, row/column selection multiplies by nonnegative integer matrices. At every composite, all siblings multiply on the left or right. The chosen factorization width remains a bottleneck, even when those other siblings contain additional old graphs. Horizontal isomorphism preserves the graph word and every endpoint-fibre witness count.

For sufficiency, every empty-word span is generated from unit restrictions and composition. Given a width-k integer factorization with k≤b, pad it to the actual old set F(A_max) of size b. The left and right matrices define finite spans with those witness multiplicities; place between them the old identity-arrow component for each letter of L. Each such old component contributes an identity matrix at F(A_max), so their composite has exactly the desired word and matrix. Finite fibrewise bijections give a semantic span isomorphism, with identity graph forest and scalar1. This includes zero matrix, empty endpoints, and a word whose letters are empty graphs. It makes no claim that that semantic isomorphism lifts to the syntax.

The carrier threshold |E|≤b also holds already in the virtual grammar: restrict the old identity span at A_max along an injection E→F(A_max) on both boundaries. Its pullback is the identity span at E. This is not a converse for arbitrary virtual horizontals.

Boolean support rank cannot replace the integer rank in the exact theorem. At b=1 the matrix [[1,1],[1,2]] has rectangular support but cannot factor through one integer coordinate; its determinant is nonzero. It does factor through two. Thus the stronger theorem detects actual witness multiplicity, not only support. Matrix-factor certificate verification is not a polynomial search or succinct span-expansion theorem.

Reran the expanded author checker successfully: 88 injective carrier restrictions and all 81 two-by-two matrices with entries in {0,1,2}, classified with widths 0,1,2 in counts 1,30,50 respectively, in addition to the earlier Boolean checks. Added independent `tests/review_integer_span_rank.py` with 22,032 factor-preservation checks and 81 actual witness-count comparisons, plus the Boolean-insufficiency counterexample. All passed.

The updated plaintext report's abstract and Section6 were also scope-checked. The abstract was asked to name the refinement-lifting requirement explicitly, rather than implying that merely fixing endpoints forces partition rigidity. Section6 correctly limits the exact image theorem to ordinary horizontals and disclaims syntactic normal forms, semantic-isomorphism lifting and cell fullness.

## Final source freeze checked

All requested mathematical corrections above were applied and reread. Separate proof-review verdicts are PASS for the five listed files, under their respective explicit scopes, including the strengthened horizontal-image theorem.

* `C5_Fixed_Endpoint_Kernel_Classification.md`: `a07a99fd790c7ebb7779906a494954721c79cb0bf31b4a6bf8e898eb2127cdc0`
* `Generation_Boundary.md`: `a6808a463b3b8114d4534bf20f5f749acb973b76b61826c2fa821b603e9dc6ce`
* `KernelPair_Provenance_Repair.md`: `ff831d272fd6f9b532e00ed59194a224d269b647506903aa418715813b74682e`
* `Original_Cut_Scalar_Memory.md`: `687249869323bb9a9751fd590f9fb75c88315df905cb69042086aacaa4d04ada`
* `Original_Envelope_Quotient_Bridge.md`: `efca8d813489164da3207c61416747cac58ad8aacbb3e53dcf5ccd5c210e203a`
