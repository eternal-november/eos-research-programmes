# Conservative modular amalgamation of occurrence-sensitive graph presentations

31 October 2026. Complete author synthesis, with acceptance recorded separately by independent review. Selected original I1 scope, not unrestricted amalgamation and not adoption or closure of other contract obligations. Named imported dependencies and byte-exact source pins are in `dependency_manifest.md` and `dependency_manifest.json`; all new companion proofs are identified below.

## 1. The model, quantifiers and distinct constructions

Fix arbitrary N∈ℕ and a finite interface category K. Let P be the old ordered graph-cut multicategory with terminal old scalar. Colors are full components (G,f:A→B), with G a literally ordered graph on at most N vertices. Operations retain the whole G, an actual ordered partition into induced input graphs, every intervening interface object and arrow, and empty/repeated input positions. An empty output has only empty input graphs. There is no bound on arity, term depth, graft histories or equation-path length. Nontrivial examples below take N≥6 and K containing 0→1→2. The theorems hold for every N,K, not only those examples.

For a monoid L define P[L] on the same colors by adjoining a coefficient l_i to every nonempty input occurrence of an old operation. Substitution sends labels l_i,m_ij to l_i m_ij at active final input (i,j); no label is attached to an empty occurrence. This is a nonsymmetric multicategory: associativity is the equality (l_i m_ij)n_ijk=l_i(m_ij n_ijk) on each active branch; identities have unit labels. It is not the old commutative global scalar changed to a noncommutative scalar.

Its relative finite presentation adds D_H(l):H→H at each nonempty color, unit and multiplication equations, and, for each OLD generator g:(H_1,…,H_k)→H,

    D_H(l) g = g(d_1,…,d_k),
    d_i=D_Hi(l) if H_i is nonempty, and d_i=id otherwise.       (Diag)

No D is added on an empty color. In the empty-output case every d_i is identity and the equation is tautological. Retain the old equations. For finite L,N,K this is a finite added presentation over the old finite signature, even though it generates unbounded arities and depths.

The I5 enrichment theorem proves this presentation presents P[L]: induction pushes labels through old generators to active external inputs; multiplication combines them; equality is exactly equality of the old operation and of each external coefficient. The normal-form comparison is relative to the pinned old presentation and does not assume arbitrary orientations of old plus new equations are globally terminating. It also gives a strict functor P[h]:P[L]→P[L'] for every monoid map h, acting entrywise on labels. This map is faithful on every operation profile iff h is injective, provided P contains a nonempty color (equivalently N≥1 and K is nonempty in this model), so a nonempty unary identity can test h. For N=0 or empty K, no nonempty color is available and coefficient inequalities are invisible, a necessary degenerate exception.

We distinguish:

1. **Bare amalgam:** identify exactly a shared P[C] along coefficient embeddings C→A,B, imposing no proposed cross law.
2. **Mixed comparison:** over the common all-unit P, impose a declared BA-to-AB law. This is a quotient of the bare amalgam with a different universal property.
3. **Presented refinement completion:** add and quotient actual graft/equation paths using specified critical/naturality cells. This is not implied merely by the existence of either operation-level object.

The first construction has the sharp conservative same-local-data repair theorem in §§2–3. The second supplies the general finite mixed criterion and genuinely acting cut transfer in §§4–6. Their distinction prevents calling a chosen distributive-law quotient the categorical pushout.

## 2. Actual pushout lifting — new graph comparison theorem

Work in the category P↓Multi_O of nonsymmetric multicategories on the fixed color set O=Ob(P), equipped with a strict identity-on-colors map from P; arrows commute with that map and fix colors. This is the declared universal-property category. It preserves full profiles; no colors, intermediate interfaces, or repeated positions are identified.

**Theorem 2.1.** For any monoid span A←C→B with monoid pushout Q=A⊔_C B, the square

    P[C] → P[B]
      ↓       ↓
    P[A] → P[Q]

is a pushout in P↓Multi_O. Consequently a finite coefficient pushout yields an explicit finite-palette presented graph pushout. Its two operation maps are faithful if the coefficient maps are injective, and whenever P contains a nonempty color the converse holds as well.

**Proof.** For any target (T,F:P→T), define W_T to consist of families w=(w_H), where w_H:H→H is unary in T for every nonempty H; put w_H=id_H on empty H. Require, for every old generator g,

    w_H F(g)=F(g)(w_H1,…,w_Hk).                           (2.1)

Equivalently require this for all old operations: induction on generator trees proves the extension, and evaluation through F makes it independent of the old representative. Empty-output operations have only empty inputs, so impose no hidden restriction. In particular the designated nullary old units satisfy the identity equation.

W_T is a monoid under componentwise composition (wv)_H=w_H∘v_H. Indeed, applying (2.1) first to v and then w gives

    (w_H v_H)F(g)
      =w_H F(g)(v_Hi)
      =F(g)(w_Hi)(v_Hi)
      =F(g)(w_Hi v_Hi).

This uses associativity of multicategory substitution, not commutativity of unary maps; empty components stay identities. The identity family satisfies (2.1).

There is a natural bijection

    Hom_(P↓Multi_O)(P[L],T) ≅ Hom_Mon(L,W_T).               (2.2)

An interpretation sends l to the family of images of D_H(l). The unit/table equations give a monoid homomorphism, and (Diag) gives membership in W_T. Conversely any such homomorphism interprets the old generators by F and each D_H(l) by its indicated component. Every defining relation holds, so the relative presentation yields one strict map P[L]→T over P. These constructions are inverse because old and D generators generate P[L]. Thus no semantic equality has been silently added.

Now compatible maps P[A],P[B]→T correspond by (2.2) to compatible monoid maps A,B→W_T agreeing on C. The monoid pushout gives a unique Q→W_T, hence a unique P[Q]→T. This proves the graph pushout property constructively. Operation faithfulness follows from the P[L] normal forms. If a coefficient map identifies x≠y, the two labels on the unary old identity at any nonempty H witness failure of faithfulness. ∎

This proof establishes a one-dimensional universal property in the explicitly stated category. No double-categorical, bicategorical or unrestricted two-dimensional pushout universal property is inferred. The common P[C] contains actual graph cuts and interfaces even when C is trivial, and contains shared nontrivial coefficients when C is not.

## 3. A sharp finite bare-amalgam family and same-input repair

The complete coefficient proof is `interface_pushout_theorem.md`; we state its data and proof essentials so the graph theorem has explicit, independently recognizable inputs.

For m≥0 let D={*,1,…,m}, E={z}. On D⊔E take partial maps with multiplication fg=f∘g. Let 0 be empty, 1 the full identity, e=id_E, c:z↦*, and y_S the identity on {*}∪S, S⊆[m]. Put p=y_∅ and

    A_m={0,1,e,c}∪{y_S:S⊆[m]}.

Its products include y_S y_T=y_(S∩T), y_Sc=c, cy_S=0, ey_S=y_Se=0, ce=c, ec=c²=0 and e²=e. Thus |A_m|=2^m+4. Let C={0,1,e,d,c} with d²=d, dc=c, ce=c, e²=e and remaining products among e,d,c zero. Let B={0,1,e,d,c,u} be the two-by-two matrix-unit monoid with external identity on {*,z}; u:*↦z, d=id_{*}. In particular cu=d, uc=e, ud=u, du=0, eu=u, ue=u²=0.

Every J⊆[m] gives an injective interface i_J:C→A_m by d↦y_J, fixing the other four elements. The other interface is C⊂B. Both locals and the common theory have finite convergent multiplication-table presentations: each adjacent pair reduces to its product, associativity joins all triples, and length decreases.

**Theorem 3.1 (exact interface boundary).** The coefficient pushout Q_J has size 2^m−2^|J|+6. Its A_m map identifies precisely the block I_J={y_S:S⊆J} and no other elements. Its B map is injective. Hence both maps are faithful iff J=∅. For J=∅ their intersection is exactly C. Whenever P contains a nonempty color, the identical statement holds profilewise for the corresponding P[-] maps, with failure already at a nonempty unary identity. For all N the pushout construction of Theorem 2.1 applies.

**Proof outline with explicit universal construction.** M=A_m∪{u} is a concrete partial-map monoid; its new cross products are uy_S=u, y_Su=0 and cu=p. For J=∅, compatible f:A_m→H,g:B→H force

    g(u)f(y_S)=g(u)f(p)f(y_S)=g(u),
    f(y_S)g(u)=f(y_S)g(e)g(u)=g(0).

These are all cross products not already internal to an input. Hence there is one homomorphism M→H extending f,g, proving M is the pushout. The uses of 0 occur inside known input images; no globally absorbing image-zero is assumed.

For arbitrary J, collapse just I_J in M. It is a congruence: y_T sends the block into itself, while c,e,u act constantly on each relevant side. The resulting quotient Q_J admits the required cocone. Every compatible f,g satisfies

    f(p)=f(p y_J)=f(p)g(c)g(u)=g(c)g(u)=f(y_J),

since pc=c. Therefore f(y_S)=f(p) for every S⊆J. The cocone also agrees at p, so the J=∅ universal map M→H exists and factors uniquely through Q_J. This proves its universal property and the exact absence of other identifications; the count follows. Apply Theorem 2.1 and operation normal forms to lift it. ∎

For full J=[m], m≥1, the 2^m different y_S become equal, and Q_J≅B. The raw union already has an unjoinable mixed local-table peak

    y_S c u → c u → y_[m],
    y_S c u → y_S y_[m] → y_S

for S≠[m]. These are distinct pure-A irreducibles. B remains faithful; independent checking on both sides must report this asymmetry, not claim both collapse. The optional null-ideal family in the frame exhibits collapse of both inputs, but is unnecessary for this sharp main boundary.

**Useful repair:** keep exactly A_m,B,C and change only C→A_m from d↦y_[m] to d↦p. Then M is the genuine finite pushout, both inputs are faithful, and the peak joins because y_Sp=p. This is explicitly an interface-embedding change, not an unnoticed alteration of a local theory. It remains nontrivial: common c,e,p are identified and cu=p, uc=e are noncommuting mixed operations. The graph common subtheory is the full P[C], with all old graph and interface operations retained. There is no disjoint-signature reduction.

## 4. A finite complete mixed-law criterion and noncommuting positive family

Let finite A,B and λ:B×A→A×B be supplied tables. Write λ(b,a)=(L(b,a),R(b,a)). Impose the mixed equation B_b A_a=A_L(b,a) B_R(b,a) at every nonempty color, alongside the local table/unit/diagonal equations. Define Q_λ by these coefficient equations. This is universal among cocones over the common P satisfying the specified mixed equations; the bare pushout does not impose them.

`twisted_normal_forms.md` proves the following complete criterion. Unique AB normal pairs A×B exist iff:

    λ(1,a)=(a,1),   λ(b,1)=(1,b);                         (U)
    λ(b,aa')=(cc',d') when λ(b,a)=(c,d), λ(d,a')=(c',d'); (BAA)
    λ(bb',a)=(c',d'd) when λ(b',a)=(c,d), λ(b,c)=(c',d'). (BBA)

Coefficient rewriting terminates by (length,BA inversion count). The only binary overlaps are AAA,BBB,BAA,BBA; the remaining overlaps are units. Thus these finite checks prove confluence; necessity follows because each peak must have equal normal pairs. The product is

    (a,b)(a',b')=(a L(b,a'), R(b,a')b').

Both pure-factor maps are injective. The criterion is iff for full unique AB normal pairs, not iff for separate pure-factor injectivity in every possible failing comparison.

The relative graph presentation is P[Q_λ], by pushing coefficient words to active inputs within each operation and using coefficient equations there. The essential new square starts at D^B(b)D^A(a)g. Mixing then distributing places the same λ(b,a) at every active child; distributing then mixing separately at all those occurrences gives exactly that same tuple. Empty children get identities. Same-channel multiplication versus distribution works identically. This square is correlated across all descendants; no independent per-child choice is introduced.

Take A=C_n and B=C_2 with inversion α_s(a)=a^(−1), n≥3. Then λ(b,a)=(α_b(a),b) satisfies the criterion and

    (a,b)(c,d)=(a α_b(c),bd).

This is genuinely noncommuting and conservative. The broader cyclic relation sa=a^r s has exact comparison Q(n,r)≅C_gcd(n,r²−1)⋊_r C_2. Both locals embed iff r²≡1 mod n; the ssa peak supplies the obstruction. For r=2,n=5^k all C_n distinctions collapse. Replacing just the mixed law by inversion repairs that comparison while preserving both inputs and old common P. This sharp additional boundary does not replace the bare-pushout boundary in §3.

## 5. Complete occurrence-refinement coherence and transfer criterion

The full independently generated construction and proof are in `refinement_coherence.md`. This section fixes its exact theorem and summarizes the proof, including the extra laws that operation confluence alone cannot supply.

### 5.1 The terminating typed presentation and its finite mixed diagrams

For the λ-positive case use old binary cuts c and designated empty/id nullaries u, with old association/unit rules R,UL,UR; old terminal-scalar decoration is omitted as definitionally identity. Add A_a,B_b unary coefficient generators at nonempty colors, their unit/table rules, BA sorting and downward diagonal rules X_q c→c(X_q^left,X_q^right), putting identity at empty children. Each frontier variable occurs exactly once; copying a coefficient label is not copying a variable subtree. There is no coefficient-over-nullary redex because u has empty output.

A genuine contextual termination measure is the lexicographic tuple (D,B,A,C,I): D is the total number of old structural vertices below coefficient vertices; B is binary-vertex count; A sums binary vertices in every binary left subtree; C is coefficient-vertex count; I counts B-before-A inversions in uninterrupted unary chains. Diagonal decreases D; R preserves D,B and decreases A; old units do not increase D and decrease B; coefficient unit/table rules do not increase D and decrease C; sorting preserves earlier coordinates and decreases I. Thus termination is not presumed from separate local termination. Irreducibles are the old canonical right comb with one AB normal pair at each active external input. Soundness and injectivity of this form prove object confluence.

Fix syntactic critical homotopies with the following exhaustive sources:

- the old R/UL/UR critical triangles and pentagon;
- coefficient AAA,BBB,BAA,BBA and unit overlaps;
- X_p X_q c: multiply/distribute versus distribute/multiply at every active child;
- X_1 c: delete versus distribute/delete at every active child;
- B_b A_a c: sort/distribute versus distribute/sort using the same λ(b,a) at every child;
- X_q l for old association or unit l→r: rewrite/distribute versus distribute/rewrite with the same coefficient on all nonempty template variables.

Add disjoint-redex and variable-overlap squares. This is complete because nonvariable proper heads of the finite rule left sides are only an old c/u or an adjacent coefficient; the six classes exhaust those unifiers. Empty children get identity on both sides; old unit children are never decorated. The companion states the actual joining words/finite schemas, not just equality of semantic endpoints. Well-founded induction comparing first steps then proves any two positive normalization paths equal modulo these cells. Adding equation inverses gives the unique ordinary equation comparison κ(t,u)=ν_tν_u^−1 whenever the normal objects agree. This is equality in the specified homotopy quotient, not literal equality of directed words.

### 5.2 Independently generated mixed completion

At fixed whole W form a category with RAW presentation trees as objects. Generating edges are actual primitive-corolla grafts at specified external occurrences, contextual equations with their rule/address/substitution data, and inverses of equation edges only. Quotient the free category by equation inverse cancellation, raw graft interchange/identities, the above ordinary homotopies, and two additional finite-rule context schemas:

    e;R(U,G)=R(T,G);e[G]                                  (MOut)

for equation e:T→U and one frontier graft G, and

    R(T,i:l);T[e]_i=R(T,i:r)                               (MIn)

for each bare rule template e:l→r inserted at one actual source occurrence. This includes the new diagonal, sorting, table and unit templates. It does NOT declare arbitrary semantically equal forests equal.

MOut extends to finite forests and equation words by induction. To derive MIn for an equation inside an arbitrary substituted forest entry, factor its construction into the surrounding one-hole forest, the bare template and its variable-substitution forest. Move the equation past the last part by MOut, apply bare MIn, and reassemble with raw graft composition. Occurrence linearity makes this valid even at repeated types and empty/nullary positions.

Every mixed path p:T→U therefore has the derived canonical form

    R(T,F↓);ν_(T[F↓]);ν_U^−1,                              (5.1)

where F↓ is the tuple of individually normalized forest entries at the ORIGINAL source occurrences. This retains each entry's own output, frontier length and ordering, actual partition, grade/interface path and coefficient array. It does not normalize only the final outer composite.

Define Ref(P[L],W) independently: objects are semantic operations, and an arrow α→β is a FULL tuple γ_i at the original inputs satisfying α[γ_i]=β. Evaluation sends grafts to their actual tuples and equations to identities. It respects all the defining relations, including MIn entrywise. Conversely a semantic tuple γ has the syntactic representative R(T,(Nγ_i));κ(T[(Nγ_i)],U). Formula (5.1) proves these hom maps are inverse. Consequently the raw-object completion is fully faithful and surjective on semantic objects, hence an equivalence; its full subcategory on normal objects is actually isomorphic to Ref. Calling the raw-object comparison an isomorphism would incorrectly identify distinct bracketed object expressions.

### 5.3 Complete certificate criterion and conservative local transfer

At fixed actual source/target profiles, two presented refinement certificates are equal iff their complete original-slot normal-entry families agree: the old partition, each entry's own full frontier and grades, and each active coefficient pair all agree. This is necessary AND sufficient by the independently constructed comparison. It is a finite algorithm on any given finite history and covers unbounded history/depth/profile schemata.

An A-local certificate is represented globally by pairs (a,1), a B-local one by (1,b). The local completion constructions use the corresponding subsets of rules; their diagrams commute with evaluation on actual generators and full tuples. Both maps are faithful and reflect equality of local certificates because both coefficient embeddings are injective. A global certificate has a specified local representative iff its endpoints and all normal entries lie in that local coefficient image; sufficiency constructs those local entries and applies (5.1). For λ-data, compute actual normal pairs, not independent deletion of mixed letters.

The same theorem covers EVERY finite coefficient monoid L by taking one channel L and the other terminal (or simply dropping the absent channel and sorting). Thus it supplies the completion and full-tuple equality test for the genuine finite pushouts Q_J in §3, not only the mixed comparison. Injective coefficient maps induce faithful full-tuple refinement comparisons; in the repaired case both local theories retain their refinement certificates. No extra two-dimensional pushout universal property is claimed.

**Chosen output presentation.** For the bare pushout Q_J, the output used here is the independently specified FULL Q_J multiplication-table presentation (with the old graph/diagonal rules), equipped with its own critical homotopies and MOut/MIn completion. It is not the uncompleted raw union of the two input path presentations. Each local coefficient generator maps to its Q_J image; each local table/unit/diagonal equation maps to the corresponding target equation, followed by a fixed unit-normalization path when required. Images of local critical diagrams agree by the independently proved target ordinary coherence, and local graft naturality maps to target MOut/MIn. These explicit comparisons retain local certificate equality faithfully when the coefficient embedding is injective. The one-dimensional pushout theorem proves that this chosen output presents the same OPERATION calculus as the raw union. It does not prove that the raw union's original equation paths already have the same homotopy quotient. Such a stronger raw-union path comparison would require adding and comparing derived mixed rules and their defining higher cells; it is not asserted or needed for this selected output-completion theorem.

A refinement arrow does not retain every intermediate factor of every execution history. For a marked cut certificate, keep the entire marked old tree and normalize inside EACH marked factor separately; no normalization crosses a marked boundary. The same operation bijection gives a bijection on labelled marked records, with all vertex substitution equations checked. Equality of flattened refinement arrows is not equality of these richer records. The foreign-factor counterexamples in §6 concern this cut fullness issue; they do not by themselves prove nonfullness of flattened Ref inclusions.

### 5.4 Negative controls and sharpness

Removing MIn breaks the full comparison even if all ordinary critical homotopies and MOut remain: assign weight 1 to each primitive graft, 0 to equations. All retained relations preserve total weight. At a nonempty identity leaf, graft A_1 then delete it by its equation. This loop and the identity have the same semantic refinement tuple but weights 1 and 0, so remain distinct. Bare A_1 MIn supplies exactly the missing equality. This proves the inner compatibility family is substantive.

A sharper mixed control removes ONLY sorting MIn in the inversion C_3/C_2 case. Give an A_(a^j) graft at H weight |V(H)|j modulo 3, and all other grafts and equations weight zero. Every remaining relation preserves weight: table rules add exponents, diagonal uses the partition identity |V(H)|=Σ|V(H_i)|, and ordinary/MOut relations preserve grafts. At a one-vertex leaf, graft B_s A_a then apply sorting, or directly graft A_(a^2) B_s. They have the same raw endpoint and semantic tuple but weights 1 and 2. Thus the missing MIXED inner law is essential even with all other inner laws and ordinary coherence retained.

Equal endpoints also do not determine a refinement arrow. Give an old source two consecutive empty/id input occurrences alongside a nonempty occurrence. Delete the first empty occurrence by u and keep the second identity, or vice versa. The final operation/profile is the same, but original-slot tuples (u,id) and (id,u) differ. The normal-entry criterion separates them even with every active coefficient unit. For marked cuts, successive nontrivial inverse labels likewise cannot be erased merely because their product is unit.

A coefficient-sensitive parallel-arrow control takes A={1,0} with absorbing 0 and B=C_2 with commuting λ. At source and target T=A_0(x), identity has entry 1, while grafting A_0 then multiplying back to T has entry 0. Both have the same complete final operation and root coefficient 0, but their original-slot entries differ.

Finally failure of U,BAA or BBA identifies distinct claimed pair normal forms already on a nonempty unary profile. Hence no comparison to the stated pair-labelled refinement model can exist. This is the exact complete mixed-coherence boundary for that normal-form target, not a claim that every failed mixed table collapses both pure local inputs.

## 6. Joint cuts and interface transport — separate exact conditions

The complete companion proof is `cut_transport.md`. Its claims concern literal fully typed records and become statements about presented certificates through §5's comparison; no directed path equality follows from a product formula alone.

### 6.1 Exact action-aware cut transfer

Fix an ACTUAL finite old cut tree T, retaining every intermediate factor operation, full profile, graph restriction, interface arrow and occurrence. For semidirect coefficients C=A⋊_αB with α:B→Aut(A), label each active edge e by (a_e,b_e). Let β_e be the ordered B-product on edges strictly above e, and put t_e=α_(β_e)(a_e). Expansion on every root-to-leaf branch gives

    ∏_path (a_e,b_e) = (∏_path t_e, ∏_path b_e).

Therefore for each prescribed actual source coefficient tuple (x,y) there is a bijection

    W_C(T,(x,y)) ≅ W_A(T,x) × W_B(T,y),

sending the original record to the full t- and b-arrays. The inverse uses the entire B record to compute β_e and then a_e=α_(β_e)^−1(t_e). It does not make separate choices for a shared parent edge. This is a B-dependent coordinate bijection on a fixed tree, NOT a calculus projection to A. In the selected partition model every nonempty edge has an active final descendant; nonempty outputs cannot be deleted by an empty/nullary cut.

At a two-level cut this says simultaneously for all j,

    x_ij=a_i α_(b_i)(c_ij),   y_ij=b_i d_ij,

with one shared (a_i,b_i), and transported A inner labels t_ij=α_(b_i)(c_ij). For a retained subtree below ancestor prefix γ, its intrinsic A coordinates are reset at prefix 1; ambient coordinates are α_γ of those intrinsic coordinates. Thus inverse transport recovers EVERY intermediate factor and not merely the final root composite.

Insertion respects these arrays: multiply the inserted intrinsic A coordinates by the common action α_γ and retain the B arrays. Contraction respects them because

    α_γ(a) α_(γb)(c)=α_γ(a α_b(c)).

Disjoint insertions concern distinct occurrences; nested insertions agree by α_γα_δ=α_(γδ). These identities prove naturality for every finite tree/forest. When a contraction deliberately forgets an internal factor, it need not be injective; marked retained factors are never silently contracted by this comparison.

For quotient-valued certificates, exact common skeleton and exact B edge records suffice to untwist matched A records. Coarser B observations require invariance of retained A predicates under every action difference within a B class AND simultaneous matching of shared parent choices. Separate marginal matches are not enough. No coarsest-I5-repair reflection is imported through a nonexistent π_A homomorphism.

### 6.2 Local cuts, fullness and old-language existence

For an injective coefficient map i:D→C,

    W_D(T,z) ≅ {w∈W_C(T,i(z)): every retained factor lies in i(D)}.

The inverse applies i^−1 entrywise. This proves exact transfer in the declared all-local-factor language and reflects equality of those records. Module membership/provenance must be retained when multiple images overlap. It does not erase mixed witnesses from the ambient theory.

Unrestricted fullness fails in the noncommuting positive examples. In a semidirect group, an A-local unit has cut (1,s)(1,s^−1); a B-local unit has cut (a,1)(a^−1,1). In the repaired bare pushout M_m, the A_m-local p has global cut cu=p with u∉A_m. Each is an actual unary cut at any nonempty old color. A sufficient and, for the unrestricted binary unary cut language, necessary condition for full fibres is factor closure:

    xy∈i(D) ⇒ x,y∈i(D).

Induction along each active path proves sufficiency for all finite trees in the present non-erasing model; every coefficient-bearing edge lies on some active root path. This criterion is additional to equation conservativity and is generally false for the displayed positive amalgams.

Old coefficient-blind existential cuts are preserved and reflected independently: any fixed old cut of a source lifts by units on internal active edges and the source labels at final active edges; forgetting labels gives the reverse implication. This preserves neither counts nor a chosen labelled witness.

### 6.3 Explicit interface tests and all-tree lifting

For proposed coefficient maps f:A→A',g:B→B', the pair map is a semidirect homomorphism iff f,g are monoid homomorphisms and

    f α_b = α'_(g(b)) f   for every b.

Necessity follows on pure-channel products and (1,b)(a,1); sufficiency follows directly from multiplication. More generally the λ criterion is (f×g)λ=λ'(g×f). These are finite table checks. They must be combined with the old transport's actual source/target, ordered occurrence, empty/active, grade and restriction squares; coefficient equivariance cannot repair invalid old geometry. For a family of transports additionally check identity and composition laws.

These conditions give preservation of operations, full refinement records and cuts. Invertible coefficient and old transports give bijective reflection. Noninvertible ones require an independent lifting test. For h:D→E define, whenever h(x)=qr,

    L(q;x,r)={p∈D: h(p)=q and ∃v∈D with h(v)=r and pv=x}.

For a target outer coefficient q with child factors r_j over specified source tuple x_j, an exact simultaneous lift exists iff

    ⋂_j L(q;x_j,r_j) ≠ ∅.                                  (6.1)

Choose one p in the intersection, then witnesses v_j; this is also necessary. Individual nonempty sets do not suffice. Since D,E are finite, only finitely many distinct constraints (x,r) occur; all subsets give a finite, possibly exponential, sufficient check covering unbounded arity. For the actual graph language one may instead check just realizable shared-parent tuples, using its occurrence constraints; a nonrealizable formal star is not a counterexample. Recursive application at the chosen actual child sources proves all finite-tree lifting. The old geometry needs its own fixed-source lift and compatible occurrence maps, automatic for an old isomorphism but not for arbitrary restriction.

A useful noninvertible positive case is a surjective group homomorphism h:G→H. For any p∈h^−1(q), choose v_j=p^−1x_j, so every set in (6.1) is the same full nonempty fibre. Conversely all fixed-source unary cut lifting forces surjectivity, by the target cut 1=q q^−1 at source 1. Thus surjectivity is the exact all-root coefficient-cut criterion for groups. For inversion semidirect groups the maps C_n⋊C_2→C_d⋊C_2 induced by reduction modulo d|n are genuine noninvertible examples when d<n; combined with an old geometry isomorphism they reflect existential cuts, but do not give unique lifts or proof-path injectivity.

In M_m, every permutation σ of ordinary coordinates induces a monoid automorphism y_S↦y_(σS), fixing 0,1,e,c,u, hence literal tree/certificate transport along an old isomorphism. By contrast restriction to a proper coordinate subset V⊊[m] defines a surjective homomorphism

    h_V:M_m→M_V,   y_S↦y_(S∩V),

which preserves all equations but fails cut reflection. Choose k∉V. The source y_{ {k} } maps to p, whose target cut is cu=p. The only preimages of c,u are themselves, and cu=p≠y_{ {k} }; no lift exists at that source. Consequently unrestricted all-root cut lifting holds iff V=[m]. Repair by retaining all coordinates, or declare only forward preservation/verified restricted cut language. This is a separate sharp interface-restriction boundary, not a failure of the positive operation embedding theorem.

## 7. Nontrivial six-vertex shared-graph calculation

Let K contain arrows h:0→1 and k:1→2. Take graph G on 0,…,5 with edges {1,2},{3,4},{0,5},{2,3}, ordered blocks U_1={0},U_2={1,2},U_3={3,4},U_4={5} and arrow profile (h,id_1,id_1,k). The second and third components are identical two-vertex edge types but distinct occurrences; cross-block edges remain in the retained whole.

Use inversion coefficients C_5⋊C_2 in additive notation: (x,ε)(y,δ)=(x+(−1)^ε y,ε+δ). On occurrence 2 choose outer label (1,1), and refine its two vertices with inner labels (2,0),(3,1). The two final labels are (4,1),(3,0). For the same inner pair under occurrence 3 with outer label (1,0), the labels would be (3,0),(4,1). They must not be interchanged merely because the input component types coincide. The corresponding transported A inner factors under occurrence 2 are 3,2, while the B factors retain outer 1 and inner 0,1. In particular naively projecting the first product to 1+2=3 is wrong: the true A coordinate is 4.

This calculation uses a real branching old cut, two repeated component occurrences, nonidentity interfaces, and a nontrivial action. All empty occurrences may still be inserted via the old designated nullaries, without coefficient labels. Removing edge {0,5} changes the retained whole and is not an equation of this theory. The final test suite must replay this fixture and the marked-factor negative controls, not merely group tables.

## 8. Assurance, baseline and scope

The monoid-product criterion is standard distributive-law/Zappa–Szép algebra; finite monoid nonamalgamation is classical. Ordinary convergent rewriting plus critical homotopies is an existing coherence mechanism. Structured/decorated cospans provide composition frameworks, not this particular faithfulness or full occurrence-refinement transfer automatically. `baseline_comparison.md` pins the primary comparisons and limits novelty claims.

The added target here is the explicit full-profile graph pushout lift, exact finite interface-embedding boundary and conservative repair, independently generated occurrence-refinement comparison, and correlated action-aware cut/interface transfer with sharp nonfullness boundaries. Scripts verify finite regressions; all-parameter proofs and independently reviewed companion theorems carry the mathematical claim. No Lean formalization is asserted. This synthesis is now complete at author-proof level; independent correctness and original-floor scope reviews are still required before full selected-I1 acceptance.
