# Structural related-work audit — 28 October 2026

## Finding

The proved structural work belongs primarily to **nonsymmetric coloured operads/multicategories, higher-dimensional rewriting, virtual equipments, and decomposition-space theory**. The strongest demonstrated reductions are the free-calculus and semantic-refinement infrastructure, pure equation-path coherence, and the exact all-degree 2-Segal construction. The concrete mixed presentation, conservative-envelope comparison, enlarged all-span presentation, and graph-dependent quotient/cut-repair package have additional proof obligations that the general baselines do not discharge merely by being cited.

The most defensible potentially distinctive integration is the **selective graph-dependent forgetting of coefficient maps, while retaining prequotient span relabellings, together with the resulting exact cut-isotropy calculation and coherent certificate repair**. Its ingredients include elementary congruence, retract, pullback, and torsor arguments. This audit does not establish priority for that integration. “No implication bridge established” means unresolved comparison, not novelty.

This is a bounded primary-source positioning audit, not a fresh full proof verification, contract amendment, or scientific-significance acceptance. Historical acceptance remains explicit for A1–A3, B1–B2 and C3. A4/B3/C5 technical verification is not their full contractual acceptance. The Oct25 structural package records nonauthor AI review of its exact scopes, not human certification or Lean verification of every new theorem.

## Evidence matrix

| Cluster | Proved result being compared | Strongest checked baseline | Classification and residual |
|---|---|---|---|
| 1. Typed calculus and refinements | Arbitrary-signature free/presented calculus; occurrence-sensitive raw forests; potentially nonthin semantic tuples | Leinster §2.3 and Thms 6.5.1/6.5.4; forest-category/opposite-slice identification | **Known theorem/direct specialization** for free/presented machinery and the semantic category; concrete formalization, execution correspondence, and counterexamples remain project work. |
| 2. Graph–monoid presentation and mixed coherence | Seven local term rules, full cut normal forms; 18 pure coherence diagrams; mixed entrywise normal forms and equivalence with semantic refinements | Mimram Props 3.16/3.20; Squier/Guiraud–Malbos Thm 4.3.2; Trnka Def 5, Prop 9, Thm 26 | Pure coherence implication is a **direct specialization once its actual hypotheses are proved**. Complete mixed local basis is a **concrete proof/instance**, not established as a direct corollary of Trnka. |
| 3. Chosen envelopes and conservative comparison | Separate free virtual/ordinary chosen envelopes; interpretation categories including transformations; reflection of old equality and unary isomorphism existence | Cruttwell–Shulman Defs 3.1/5.1/7.1 and Thm 5.2; Shulman Thm 4.1 | **Concrete construction/proof using established doctrine**. A theorem-level reduction of the entire free-plus-conservative package is **unclosed**. Reflection is not fullness. |
| 4. Enlarged all-finite-span presentation | Complete all-boundary normal forms; local section presentation of activated quotient; marked interpretation-category property | Equipment/diagram calculus; ordinary term-quotient universal properties; Myers Thms 2.4.2/3.3.1 for diagrammatic soundness | **Concrete instance/presentation**, possibly useful integration. No checked generic theorem supplies these exact normal forms. It names additional spans/squares and is not the C5-only envelope. |
| 5. Exact all-degree cuts | Scalar-one exact simplicial groupoid, every triangulation/unit comparison, original discrete finite-K slice | GKT Thm 5.8 + DK Prop 2.5.3 and Examples 2.5.4(c), with explicit product bridge below; Walde v5 Cor 4.4.1 | **Direct specialization/concrete integration** for 2-Segal property. Original-slice recovery and exact-operation identification require the source's additional comparison proofs. |
| 6. Activated quotients and laminar repairs | Induced-upward iff congruence; local generation; exact retained-symmetry isotropy; contraction criterion; coherent marked repair; sharp finite marking bound; actual-bijection transport | Span/relation quotient theory; elementary retract and action-groupoid/torsor facts; equipment base change | **Possibly new integration, priority unresolved**. Elementary bounds/transport principles are not new general theories. No checked source yields the entire graph-selective, retained-symmetry theorem. |

“Concrete proof/instance” below is not a claim that the proof or instance has never appeared elsewhere.

## 1. Free/presented coloured calculus and semantic refinements

### What the source proves

Original `research/workstream_A/A1_RepresentationProof.md`, `A1_CalculusComparison.md`, `A2_AdjunctionProof.md`, and `A3_PresentedUniversalProof.md` cover arbitrary interfaces and component quiver, complete ordered path profiles, arbitrary generating collections and independent target operation universes. They allow repeated occurrences and enabled nullaries without imposing finiteness or decidable equality. The free extension has the full hom correspondence, naturality and adjunction. The presented quotient uses the **least declared parallel substitution congruence**, not equality in a chosen model. Completeness against all models uses a universe containing the quotient itself.

B1/B2 (`B1_PrefixChronology.md`, `B2_GeneralComparison.md`, `B2_QuotientCertificate.md`) distinguish raw forest arrows from semantic operation tuples. Raw fixed homs are thin; semantic homs need not be. The associativity quotient has distinct refinements `([μ],[1])` and `([1],[μ])` with equal composite endpoints, and a fixed-target failure of lifting from raw syntax.

### Checked baseline and actual mapping

Leinster's fixed-colour free-multicategory theorem applies to a suitable monad on a suitable category; Set and its finite-list monad satisfy the stated hypotheses. His §2.3 also constructs the free strict monoidal forest category of a plain multicategory. [Primary text, §2.3 and Thms 6.5.1/6.5.4](https://arxiv.org/pdf/math/0305049)

**Bridge:** take colours `(A,B,c)` and assign empty operation sets to inadmissible lists; admissible lists are exactly composable paths with the output endpoints. Substitution preserves admissibility, including deleting a nullary loop slot. The source proves inverse path/list translations on operations and strict maps. Its free trees are therefore the fixed-colour free construction restricted to this substitution-closed profile class. For presentations, taking the least parallel congruence, quotienting each fibre, and descending free interpretations proves the usual presented universal property. The quotient model supplies the converse of all-model soundness. These are standard algebraic arguments with their necessary inputs supplied, not a novel semantics-completeness principle.

For a calculus `P` and fixed output `W`, let `F(P)` be its forest category, with forests directed from concatenated inputs to outputs. Then

`Ref(P;W) ≅ (F(P)/(W))^op`.

An object is an operation `a:p→W`; a refinement is a forest `b:q→p` with `a b=a′`. This is precisely an opposite slice arrow, retaining each forest entry's full profile and nullary allocation. Equivalently it is a category of elements of the substitution action. This explicit formula proves the comparison, rather than relying on a name.

### Residual and classification

**Known theorem/direct specialization**, plus detailed implementation and concrete certificates. Raw-thinness does not imply recoverability: every functor from a thin source is faithful on fixed homs even when it collapses tree objects. The legal-execution/ancestry-poset correspondence, exact occurrence transport, and demonstrated quotient nonlifting remain actual useful proofs; their correctness does not depend on being novel general category theory. Nothing here says that slicing commutes with an arbitrary presentation quotient or proves B3's independently specified mixed local presentation.

## 2. Graph–monoid presentation and mixed coherence

### What the source proves

**C1 model construction:** `Results_Workstream_C1.txt` and its uniform model proof establish the graph-cut calculus itself: components retain ordered graphs and actual K-arrows; cuts retain ordered partitions, including empty blocks; substitution lifts induced subsets and composes the entire arrow path. Both units, associativity, closure under each vertex bound, and the typed free/presented adapter are proved. Its mechanism is nested induced restriction plus category composition. **Classification: standard concrete model/instance with a project-specific typed comparison proof**, not a new general assembly principle. The GKT bridge in §5 identifies its graph-cut simplicial factor, but does not by itself certify the entire original Lean adapter or contractual finite-test floor.

`workstream_integration/proof/Completion_Comparison.md` works for every graph bound N, finite category K and finite commutative M, with unbounded arities, terms and histories. Its term rules are rotation, left/right unit deletion, scalar identity/multiplication, and left/right scalar movement. They present full retained graph-cut witnesses with one global scalar. The mixed category is independently generated by grafts and invertible equation steps, with raw interchange, pure coherence O, and mixed MOut/MIn. Theorem 6.2 identifies path equality with equality of **normal forest entries at each original occurrence**. The comparison is an equivalence; its normal-object subcategory is isomorphic to semantic refinements. Theorem 8.1 is a necessary/sufficient **equational-entailment** criterion on the same generating graph, not a decision algorithm for arbitrary alternative relation sets.

The companion semantic proof gives homs as a disjoint union over admissible ordered runs, with scalar fibre `{(n_i):m∏n_i=m′}`. The full entry profiles, not just total product/endpoints, are retained. C3 separately proves the powerset of cross-block edges and, when placements are forgotten, the multinomial-times-powerset total-witness fibre. These are exact elementary information-loss calculations, not general empirical identifiability.

### Baselines, implication bridge and limitations

Mimram's abstract 2-ARS theorem states that weak normalization plus **filled** confluence gives coherence; termination and local filled confluence provide those hypotheses. Instantiate states as typed raw terms, steps as contextual rule instances, and fillers as the 18 joining diagrams plus independent/variable squares. The source's termination measure and exhaustive local-peak proof establish the premises. This yields pure equation-path coherence, not the noninvertible graft/equation mixed theorem. [Mimram, Def 3.14, Props 3.16/3.20](https://lmcs.episciences.org/16103/pdf)

Squier's theorem, in Guiraud–Malbos's formulation, gives a homotopy basis from generating confluences of a convergent 2-polygraph. Applying that formulation would additionally require a correct typed-tree/polygraph encoding; Mimram avoids this extra bridge. Neither theorem provides this presentation's termination or critical-pair calculation. [Guiraud–Malbos, Thm 4.3.2](https://arxiv.org/html/1402.2587v2)

Trnka's categorical-operad integration has morphisms consisting of an ordered substitution forest and an internal morphism, entrywise compatible 2-cells, and an internal/substitution factorization. Its equivalence theorem concerns **constant-free nonsymmetric Cat-operads**, indexed by nonempty ordinals and surjections. [Trnka, Def 5, Prop 9, Thm 26, v2](https://arxiv.org/html/2506.12399v2)

**Mapping:** reverse orientation to match forest-then-equation paths; internal operation morphisms match equation paths and entrywise 2-cells match changes inside inserted entries. **Unclosed steps:** full coloured/path typing, empty fibres and nullary operations; substitution on the equation groupoids; and proof that the particular seven bare MIn schemes plus elementary MOut derive all required identifications. Trnka's positive-arity theorem cannot discharge these by citation. Standard coloured multicategories already allow zero arity, so the mismatch does not itself prove novelty.

### Classification

Pure coherence conclusion: **direct specialization after genuine hypothesis verification**. Semantic scalar products and fibre formulas: **coordinate specializations**. Complete mixed finite-schema presentation and its failure controls: **concrete proof/instance**, with possible integration value but no established priority claim. The old scientific-acceptance verdict is not changed by this contextualization.

## 3. Chosen virtual/ordinary envelopes and conservative reflection

### What the source proves

`Conservative_Equipment_Envelope.md` constructs separate chosen virtual and ordinary extensions from the original C5 local presentation for N≥6, finite K and finite commutative M. The vertical base is a small full category of **tagged finite sets**, not a skeleton identifying old interfaces by cardinality. Fresh restrictions and units remain distinct horizontal expressions; the ordinary grammar also adds composites. Beta/eta factorization operations are imposed at every source arity and surrounding context, including nullary whiskering.

Restriction to the old generators is an **isomorphism of interpretation categories including cell-natural transformations** for strict choice preservation; strong preservation gives an equivalence with coherent comparisons of choices. Separating semantic equipments prove reflection of old full-profile equality, actual old tuple equality, and existence of unary globular isomorphisms between old components. The theorem does **not** prove every new old-profile cell comes from an old one.

The separate concrete `GraphSpanModel.md`, Theorem 7.1/Corollary 7.2, also gives an exact representability boundary for the full graph family: a path has an opcartesian composite iff at most one input graph is nonempty. With two nonempty inputs, either the size bound excludes every output or two wholes differing by a cross-edge block even weak universality. On the representable paths, an individual cell is opcartesian iff its coefficient map is bijective and its scalar is a unit. This concrete classification is not inherited automatically from the free ordinary envelope.

### Checked baseline and bridge

Cruttwell–Shulman supply the exact transformation and cartesian/opcartesian conventions. Their Theorem 5.2 identifies virtual double categories having composites of every finite path, including the empty path, with pseudo double categories. [Definitions 3.1/5.1/7.1 and Theorem 5.2](https://arxiv.org/pdf/0907.2460)

**Bridge for representability only:** the source's factorization constructors and beta/eta equations produce inverse maps on all the relevant cell sets; these are exactly the required universal properties. Thus the ordinary-envelope representability conclusion follows from that theorem. This is not a published free-envelope construction merely because the definitions match.

Shulman's Theorem 4.1 equates the framed-bicategory restriction/fibration condition with companion/conjoint data; canonical base-change comparisons arise from universal uniqueness. [Shulman, Thm 4.1 and §6](https://arxiv.org/pdf/0706.1286)

**Residual:** neither checked theorem as stated supplies this fixed-base presentation, extension on transformations, nor witness-sensitive conservativity. The source separately constructs these and separates old data using the faithful regular realization `F(A)=∐_C K(C,A)`, graph spans, and an unnormalized graph-word envelope. An old one-entry empty graph is not the empty word. Full recovery in the *separating model* is the premise used to reflect equality in the free envelope; it is not fullness of its unit.

### Classification

**Concrete construction/proof within established equipment doctrine; whole-theorem direct-corollary comparison unresolved.** It is a genuine two-dimensional universal result, not “no universal property yet.” Its scope also must not be upgraded to the whole original E2/E4 contract. The same source's graph-word assembly is invertible only for a single identity-cut entry; arbitrary assemblies are not made exact by free completion.

## 4. Explicit enlarged all-span local presentation

### What the source proves

`Extended_Local_Presentation.md`, Theorems 4.2/7.1 and §§5–8, names **every** horizontal `(G,S)` with finite span S, every full span square, global scalar maps, binary graph cuts and actual nullary units. Finitely many kinds of local rules—span composition, scalar centrality, matched-boundary naturality, rotation and units—give normal forms `(π,φ,m)` in every fixed complete profile/outside-boundary sort. Evaluation is an isomorphism with the concrete virtual equipment. This is a small infinitary signature, not a finite total generator list, and not a claim of a convergent rewrite system on the whole raw syntax.

The span-doubling section equation at an induced-upward active graph set I gives exactly the quotient retaining π and m and forgetting φ at active outputs. Restrictions/units remain genuinely universal. Interpretation categories include transformations. Strong equipment interpretations require **explicit universal markings in the whole target**; bare equations do not force universal behavior among additional target cells.

### Strongest checked baseline and mapping boundary

The ordinary term-quotient argument explains extension of a local signature interpretation, while equipment uniqueness explains restrictions and units. Myers proves soundness/invariance under permitted diagram deformation, including a neatness hypothesis for ordinary double diagrams and an equipment version. These are soundness theorems, not completeness of the present graph/span/scalar presentation. [Myers, Thms 2.4.2 and 3.3.1](https://arxiv.org/pdf/1612.02762)

**Actual bridge needed and supplied locally:** binary trees must flatten to an actual retained graph partition, all matched coefficient squares move to the root, scalar labels aggregate without erasing nullary values, and genuine units delete only forced diagonal tuple coordinates. Normal forms compare actual finite functions within the same boundary sort. These checks explain why a generic “string diagrams are coherent” citation cannot substitute for Theorem 4.2.

### Classification and unresolved comparison

**Concrete presentation/instance**, possibly useful integration of established mechanisms. Its theorem-level comparison with a generic presentation of the product-style graph/span doctrine remains unclosed in this audit. Crucially, this is **not** the C5-only free-envelope theorem: additional spans, doubled spans and square maps are named. Their generation from the smaller old signature is not proved. The enlarged presentation closes a real local-presentation gap without closing that different bridge.

## 5. Scalar-one exact all-degree unital 2-Segal groupoid

### What the source proves

`Global_Cut_Repair.md` §§1–5 defines X_n by ordered graph partitions with empty blocks, fixed interface sets A_i, all interval spans S_ij, and actual endpoint-preserving bijections `P(S_ij,S_jk)→S_ik`, satisfying unit and associativity equations. Morphisms fix interfaces and graph data and are compatible interval-span bijections. All scalar labels here are 1. Every monotone map acts by interval restriction/merging, so outer faces and all degeneracies really exist. Every triangulation comparison and the unit comparisons are equivalences of groupoids.

### Verified implication bridge

Write `X = G_N × B`, separating graph layerings from coherent span-interval records. This is compatible with every simplicial operator, because their data and equations are independent.

1. Define a restriction species `R_N(S)` of a graph **and total order** on S, empty when |S|>N. Restriction along injections restricts both structures. The hereditary cutoff is permitted; no monoidal/disjoint-union closure is needed. GKT's construction produces structures with n layers, empty layers allowed. Choosing the increasing ordered skeleton gives precisely G_N, including its induced outer restrictions. [Gálvez-Carrillo–Kock–Tonks, Def 5.4, construction 5.7, Thm 5.8](https://arxiv.org/pdf/1708.02570)
2. B is 1-Segal: restriction to principal spans is an equivalence. Flat tuple composites give an extension, and the source's equation (3.2) extends principal-span isomorphisms uniquely to all intervals. Since B_0 is discrete, the indicated composable-string pullbacks are the required homotopy pullbacks. DK's Proposition 2.5.3 makes B unital 2-Segal, and Examples 2.5.4(c) gives product closure. [Dyckerhoff–Kapranov, §2.5](https://arxiv.org/pdf/1212.3563)

Thus the 2-Segal conclusion has a **checked baseline implication**, not just an analogy. The source's own direct gluing proof is a concrete proof of that integration.

Walde's corrected v5, Corollaries 4.4.1–4.4.2, then interprets 2-Segal spaces as invertible Segal dendroidal spaces/nonsymmetric infinity-operads. The corrected Lemma 3.1.1 requires the selected fibre subcategory to have **the same objects** as the weak fibre, an initial object, and cofinality into the left fibre. Contractibility of selected fixed-root cut groupoids is not a replacement for those hypotheses. [Walde, corrected v5](https://arxiv.org/pdf/1709.09935v5)

### Classification and residual

**Direct specialization/concrete integration** for unital 2-Segalness. The source still supplies additional exact-operation comparison (contractible choices of interval extension) and a fully faithful, degreewise discrete original finite-K/M=1 simplicial embedding using the faithful tagged graph-span realization. General theorems do not by themselves identify that embedding. Groupoid equivalences are not literal set bijections. Nor do they supply a missing exhaustive finite certificate.

The arbitrary quotient-root objects `D_T(a)` in §§6 onward form a **separate tree-indexed module**, not a full simplicial object. An arbitrary nonexact root coefficient has no automatic outer restriction. Nothing above changes that boundary.

## 6. Graph-dependent quotient, laminar obstruction, interface transport and repair

### Exact results

`GraphDependent_Quotient_and_Cut_Memory.md` proves:

- For parallel cells `(π,φ,m)`, forgetting φ precisely when output graph G belongs to I is a substitution congruence **iff I is induced-upward**. Two doubled-span sections generate it. It preserves restrictions, contextual units and original globular fibres.
- At inactive G, a scalar-one unary coefficient map is invertible iff it is bijective. At active G, invertibility instead means equal endpoint support.
- For a planar tree T, naive cut groupoids retain actual **prequotient** span-bijection arrows while omitting chosen inner bijections at active nodes. They are connected, with isotropy
  `A_x = ∏_(active nonroot v) ∏_(a,b) Sym(E_v(a,b))`.
  A contraction deletes the corresponding factor; it is an equivalence exactly when that factor is trivial.
- Retaining the actual inner bijections gives contractible certified cut groupoids with constructed coherent contractions/splits/rotations and genuine unit insertions, in every finite tree. Under finite equivariant markings over the same naive groupoid, killing stabilizers requires at least |A_x| marks; contractibility requires exactly |A_x|, attained by the certificates. The family `(S_n)^(d−1)` demonstrates unbounded order dependence at fixed active graph.

`Global_Cut_Repair.md` §§8–11 supplies the exact-operation graft action and separate nonexact comparison maps. Transport of retained certificates requires actual bijective comparisons at all relevant composite intervals. For nonempty paths, every feasible tuple must have exactly one compatible internal lift. For a nullary unit the map is `A′→A′×_A A′`, bijective iff `f:A′→A` is injective. Primitive adjacent-pair tests and root-only support-isomorphism tests do not suffice.

`TerminalRestriction_NoGo.md` separately proves a bounded retract obstruction: restrictions along terminal maps to nonempty finite interfaces have a substitution-context retraction after choosing points. Identifying two such restrictions forces equality of the old cells. This refutes the stated uniformly paired partition/coefficient equation scheme, not all coupled quotients.

The original C2 relation model constructs two genuine generic calculi, not merely test examples. **Explicit standard-instance bridge:** in the locally ordered category of finite-set relations, assign a unique multicell from `(R_1,...,R_n)` to W when their relational composite is contained in W; require equality for the exact subcalculus. Associativity, monotonicity of relational composition, and diagonal units give substitution and unit laws, including empty carriers and loop nullaries. This identifies the generic constructions as **standard concrete instances**; their occurrence-aware public Calc implementation and comparison certificates are project work. The relation model also supplies a useful weaker transport comparison: composing endpoint-restricted relations is contained in restricting their composite; internal surjections suffice for positive-arity equality, while nullary equality requires injectivity. Equal relational support does not imply bijectivity of witness sets. C2 supplied exact/containment calculi and this local transport slice, not the full arbitrary-map-class D2 converse. Later all-span and cut work provides real downstream use, so the old local report’s “not yet used in D2/E” is not a current blanket description.

### Baselines and precise mapping

**Span-to-relation quotient baseline.** Hosseini–Shir Ali Nasab–Tholen–Yeganeh's Theorem 2.3 identifies relation categories with quotients of span categories under a stable factorization system in a finitely complete category; FinSet uses surjections/injections. [Primary theorem](https://arxiv.org/pdf/2112.04599)

The active coefficient homs resemble a preorder reflection: a map between fixed finite spans exists precisely when source endpoint support is contained in target support, and two directions give equal supports. But their quotient identifies **span morphisms/cells at selected graph outputs**, retaining the horizontal spans themselves, whereas that theorem quotients span arrows as objects of the relevant hom categories. No direct-corollary bridge has been established for selective activation, multicell substitution, and the retained cut doctrine. In particular, the published span quotient does not calculate this graph-dependent active-node set.

**Elementary groupoid/torsor bridge.** A finite equivariant marking over a connected groupoid with isotropy A gives an action groupoid `L//A`. Its automorphisms are stabilizers and components are orbits. Therefore trivial stabilizers force a free action, giving |L|≥|A|; contractibility forces one free orbit, giving |L|=|A|. This is the ordinary torsor mechanism, not a new information-theoretic lower bound. The standard simply-transitive convention is recorded in the [Stacks Project, torsor definition](https://stacks.math.columbia.edu/tag/03AH). The project-specific work is the exact calculation of A from induced graph activation, demonstration that contractions project factors, and construction of a globally compatible certificate system attaining the bound.

**Base-change bridge.** The nonempty-path comparison forgets internal lift coordinates; its fibre is `∏ f_i^−1(a_i)`. Counting those actual fibres yields the stated bijectivity test. Nullary composition is a diagonal, so its test is injectivity, not a vacuous empty product. These are explicit finite-pullback calculations within standard equipment base change. They do not require, or establish, general Beck–Chevalley invertibility for all maps. Similarly the retract no-go is the elementary implication `r∘i=id ⇒ i(a)=i(b) forces a=b`, instantiated by actual cartesian lifts and permitted substitution contexts.

### Classification and exact unresolved comparison

- Induced-upward classification and section generation: **concrete theorem/instance**, with no checked general prior theorem instantiating the entire graph-selective statement.
- Torsor cardinality bound and retract implication: **known elementary mechanisms/direct specializations** once their particular inputs have been proved.
- Graph-sensitive isotropy, its precise contraction loss, all-tree repair/action, and the exact admissible interface class: **possibly new integration; priority unresolved**. Their novelty cannot be decided solely by recognizing the ingredients or by failing to find an identical statement.

The scope is planar/laminar in **occurrence runs**, not arbitrary crossing cuts. Graph blocks themselves can be nonconsecutive vertex subsets. The cut arrows deliberately retain actual prequotient symmetries; the intrinsic active scalar-one quotient automorphisms are trivial. A theory that discards those transports or takes components changes the preserved information and is not ruled out. The bound is not absolute space complexity. Inner labels and cut morphisms have scalar 1; the root may have arbitrary scalar. No blanket arbitrary-root 2-Segal or all-scalar unique-factorization theorem follows.

## Applied-system baselines: what they do and do not imply

Vagner–Spivak–Lerman construct the symmetric monoidal wiring category (Prop 3.11) and general/linear dynamical-system algebras as lax monoidal functors (Props 4.5/5.5). Thus typed hierarchical assembly and attaching dynamical semantics are established paradigms. [Primary paper](https://arxiv.org/pdf/1408.1598)

Lerman's *Networks of open systems*, Theorem 9.5, sends a map of networks of open systems to a 2-cell in RelVect, relating their interconnection maps and control-system semantics. This already treats maps between networks, not just composition of a fixed list of boxes. [Primary paper, Theorem 9.5](https://arxiv.org/pdf/1705.04814)

These prevent positioning “typed systems plus composition plus maps” as the distinction. They do **not**, without an explicit functor/presentation comparison, imply the present planar graph-cut local basis, old-profile conservative completion, or graph-activated coefficient quotient and retained-symmetry repair. Nor does the structural package establish operational control, unknown-port discovery, or empirical adequacy merely by using similar categorical vocabulary.

## Source identity and audit limits

Original source: Library ``, version 6.

Structural source: Library ``. Read `ScopeAndStatus.txt` together with the proofs. The recovery register and `Source_Identity_Check.json` distinguish original author hashes from delivered editorial copies. Current inspected structural SHA256 values:

| File | SHA256 |
|---|---|
| GraphSpanModel.md | e60be747d342fab54276900cb810ff9d9648384cb983bfe1357659838cbf4a7c |
| ScopeAndStatus.txt | 2ba05545c4e379e8d00eb55102e78d12e63a41b0f20e150d6358424804dfd134 |
| Conservative_Equipment_Envelope.md | b3335269c4080bd6c5c5dc31a370b57499c40e18a99992ec0ba2c551a1926efa |
| Extended_Local_Presentation.md | f8e4d9325e7daf2bbf3e77b18d8ea7408f34b86cb52df6226fd795902eb85e08 |
| Global_Cut_Repair.md | 2329adbd1844a9a62bfefe2094526d490c302acc639116a062590dd2d31ca449 |
| GraphDependent_Quotient_and_Cut_Memory.md | d011b91389c80c09738cefc69d09a03db88300742d00d1b1ea3bb3c1bbb3c545 |
| TerminalRestriction_NoGo.md | e4e1196e626b98948aa6841eaece4421963506a46f9dc47ea3f4dd13c2a8d468 |

The cited external theorem statements were inspected on primary full texts. The GKT/DK product mapping received a separate independent AI comparison check. Literature searching also located broader free-span/free-double-category constructions, but their exact transformation/preservation hypotheses were not fully reconciled with this presentation; they are not silently used to classify the whole envelope as a corollary. No further literature branch is required to state the present bounded conclusions. No source absence is treated as evidence of priority, and no old acceptance decision is changed.
