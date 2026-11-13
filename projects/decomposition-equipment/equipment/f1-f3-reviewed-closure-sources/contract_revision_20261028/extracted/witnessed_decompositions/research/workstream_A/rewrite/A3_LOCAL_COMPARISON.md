# Exact A3 instantiation of the mixed graph-cut presentation

Contract: v0.1, SHA256 `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.

Evidence: complete P-level local comparison, using the actual accepted A1–A3 APIs and the separately checked representative. On 2026-10-24, the non-author reviewer reported this bridge sound and assigned LOCAL_VERIFIED, with no theorem-source changes requested. No public Lean graph-signature adapter is asserted. This document supplies the previously pending LOCAL comparison; it does not discharge A4's C1 downstream-use or §3.6 B3/B4/C5 acceptance gates. Those remain OPEN, as explained in `../review/A4_IntegrationGate.md`.

The APIs inspected for this comparison are `Signature`, `Tree`, `Tree.Operation`, `Tree.freeCalc`, `Tree.generatorOperation`, `Tree.substituteOperation_generator`, `Tree.extend`, `Presentation.Equations`, `Presentation.Derives`, `Presentation.congruence`, `Presentation.quotient`, `Presentation.projection`, `Presentation.quotient_eq_iff`, `Presentation.Model`, `Presentation.extend`, `Presentation.homEquiv`, `Presentation.extend_natural`, and `Presentation.derives_iff_all_models`. The actual quotient construction is in QuotientCalculus.lean, not a postulated quotient. Artifact provenance is the accepted A3 source snapshot, `../A3_SourceSnapshot.sha256`.

## 1. The exact quiver and signature

Fix an integer N >= 6, a finite category K, and a finite commutative monoid M. These are precisely the frozen general parameters; the proof also works for smaller N. Use explicit finite carrier/composition tables when running a decision procedure. Let I be the objects of K. Write K(A,B) for its arrows, to distinguish them from the component quiver J:

    J(A,B) = {(G,f) : G is an ordered simple graph on [r], r <= N;
                         f belongs to K(A,B)}.

Install J as the quiver on I. A `Component I` is then exactly an endpoint pair together with (G,f), not merely an interface arrow, graph isomorphism class, or ambient vertex subset. Ordered graphs are equal when their vertex counts and adjacency relations on [r] agree. For U subset [r], the restriction G|U uses its increasing enumeration i_U; the literal restriction equalities are proved in THEOREM.md §1.

Define S = S(N,K,M) as this instance of `Signature I`:

1. A binary generator C(G;U,V;a,b) for every ordered bipartition U disjoint-union V=[r], including empty blocks, and arrows a:A -> B, b:B -> C. Its source/target are A,C; output is (G,ba); input is the actual two-edge `Quiver.Path` whose components are (G|U,a),(G|V,b). In the snoc representation it is `(Path.nil.cons (G|U,a)).cons (G|V,b)`.
2. A nullary generator U(A), source=target=A, output=(empty,id_A), input=`Path.nil`. No other empty-graph arrow is a nullary output.
3. A unary generator D(W,m) for every complete component W and m in M. Its source/target are W.source,W.target, output=W.edge, and input=W.edge.toPath. W need not have equal interfaces: “unary W to W” is an operation profile, not an interface arrow W.source to itself.

These data specify every field of `Signature`, including `input` and `output`, without taking a semantic operation as an unspecified generator. The signature is finite for each fixed N,K,M. Identity presentations are `Tree.leaf W`, not an additional generator. In formulas below write x_W for this identity leaf, u_A for the U(A) corolla, d_m(t) for the unary node, and c(t,v) for the binary node with the full generator label specified by the current template. That label is retained data and is not determined by its two children. Node children are indexed by the actual zero/one/two input slots; the notation does not change that indexing.

## 2. Finite declared equations in `Presentation.Equations S`

Let E_G(c,p)(t,u) hold exactly when (t,u) is one of the following finite template pairs, packed in the shared fibre `Tree.Operation c p`. There is no model-equality clause and no already-closed relation hidden in E_G.

- R: the two three-leaf binary trees for an ordered triple partition (U,V,W) of G and a composable arrow triple (a,b,c). Their outer/inner labels are exactly THEOREM.md §3: the left groups U union V first with arrows (ba,c), the right groups V union W first with arrows (a,cb), with all inner blocks pulled back by increasing enumeration. The three external children are identity leaves at (G|U,a),(G|V,b),(G|W,c).
- UL: c(u_A,x_W)=x_W for the binary generator (empty,[r];id_A,f), W=(G,f:A -> B).
- UR: c(x_W,u_B)=x_W for ([r],empty;f,id_B).
- D0: d_1(x_W)=x_W.
- DA: d_m(d_n(x_W))=d_(mn)(x_W).
- DL: c(d_m(x_X),x_Y)=d_m(c(x_X,x_Y)), for every binary generator with input components X,Y; the decorator on the right is at its output component.
- DR: c(x_X,d_m(x_Y))=d_m(c(x_X,x_Y)), with the same convention.

The common profiles have respectively three, one, one, one, one, two and two leaves. The nullary u occurring in a unit equation contributes no external leaf. An empty-colour identity leaf is still one leaf and is never replaced by u in a template. Empty blocks with nonidentity K-arrows remain genuine profile components.

Parallelism is checked before packing each template: R uses the strict restriction lemma and category associativity; UL/UR use the identity laws and empty path; the other templates keep the complete input path unchanged. These are equalities of component graphs, ordered paths and actual arrows, not just cardinality/equality of outer endpoints. Any implementation equality transports used to pack the template are the corresponding component/path equalities. Proof irrelevance affects only those proofs, not the trees. Formally E_G on an arbitrary c,p is membership in this finite family after these named transports; it does not allow additional pairs with merely equal evaluation.

The templates have identity leaves rather than arbitrary substituted terms. Thus E_G really is finite. All variable instances, contexts, and derived equations are generated by `Presentation.Derives S E_G`, rather than added as an infinite unexplained declaration set.

## 3. Agreement of the generated congruences, in both directions

Write D(t,u) for `Presentation.Derives S E_G t u`. Let t -> u be exactly the contextual oriented rewrite relation of THEOREM.md: a template is instantiated at its ordered identity-leaf positions by arbitrary well-typed trees, then used in an arbitrary one-hole tree context. Let t approximately_R u be its reflexive/symmetric/transitive closure.

First, every contextual rewrite is a D-derivation. A bare template is `Derives.equation`. Its arbitrary occurrence-wise instance is obtained by `Derives.substitute`, taking that outer derivation and reflexive derivations for every inserted tree at its independently specified replacement profile. It remains to justify context closure rather than assume it: for a parent node g, take the same `Tree.generatorOperation g` on both sides, use reflexivity for that outer corolla, and use the desired derivation at the distinguished child plus reflexivity at the other children. `Tree.substituteOperation_generator` identifies the resulting substitutions with the actual parent nodes. Induction up the one-hole context gives closure. Empty and unary input paths are covered by the same zero/one-slot construction. Reflexivity, symmetry and transitivity now give approximately_R contained in D.

Conversely, approximately_R is a parallel substitution congruence containing E_G. Each rewrite preserves the full ordered frontier, so its equivalence closure is parallel. For substitution stability, first graft the SAME prescribed forest into two terms differing by one contextual rewrite. Every template metavariable occurs exactly once on each side. Therefore the old internal cut/decoration/unit vertices still form that same redex after grafting; its metavariable subtrees have simply received their matching replacement subforests. The resulting outer context is obtained by grafting at its other leaves. No nullary template vertex is mistaken for a leaf. The canonical `Path.slotExpand` and `Tree.frontierLeafEquiv` identify these positions and preserve their component types; repeated colours do not merge positions. This proves one-step stability under arbitrary common grafts, hence stability of approximately_R by induction on a zigzag.

If two replacement forests are pointwise approximately_R-related in the SAME independently specified profiles q_i, change their finitely many entries one original occurrence at a time. Context closure propagates each change through the fixed outer tree. Original occurrence addresses, not lookup by component equality, designate the changed entry. Combining this with the preceding common-forest result proves the simultaneous outer-and-inner substitution field of `ParallelCongruence`. Thus `Presentation.derives_least E_G` gives D contained in approximately_R.

We have proved, before using completeness of any selected model,

    Presentation.Derives S E_G t u  iff  t approximately_R u.       (3.1)

This relates the ACTUAL A3 least closure to the rewrite congruence; it is not a replacement of D by a semantic kernel. It also resolves the distinction between the finite identity-leaf equation templates and THEOREM.md's arbitrarily instantiated rewrite schemas.

## 4. The independent full flat-witness target as an actual `Calc`

Define F=FlatCut(N,K,M) independently of E_G and D. For output component c=(G,f), its total operation space is the disjoint union over full paths p from c.source to c.target of the following data:

    ordered partition (U_i)_(i in Slot p) of [r], allowing empty blocks;
    for every position i, componentAt(p,i)=(G|U_i,f_i);
    the full composable arrow string (f_i), with composite f;
    value m in M.

The path p is retained as the operation's profile. “Ordered partition” is read in the left-to-right order of `Path.Slot p`; the frontier path is not reconstructed merely from a list of untyped input graphs. The whole graph G is retained by the output component, together with its adjacency data, including all cross-block edges. When p is empty, [r] must be empty, the output arrow is id_A and the outer interfaces coincide. The M-value is still arbitrary.

The identity at (G,f) has the singleton block [r], singleton arrow f, and value 1. For outer operation w and an independently chosen inner operation v_i of output componentAt(p,i), with blocks V_(i,j) in the canonical coordinates of G|U_i, define the block at the expanded profile slot corresponding to (i,j) by i_(U_i)(V_(i,j)). The actual correspondence is `(Path.slotExpand p q).symm (i,j)`, where q_i is the ENTIRE profile of v_i. Retain the concatenated arrow string and value `m * product_i n_i`; retain G and f unchanged.

This specifies `Collection.Op`, `profile`, `CalcData.identity`, `CalcData.subst` and their profile laws. The two unit proofs are whole-set restriction and the monoid/category units. For associativity, the two `CalcData.composeFamily` routes identify a final position with the SAME ordered triple (i,j,k), using the accepted occurrence transport. Its block on both routes is i_(U_i) i_(V_(i,j))(W_(i,j,k)); increasing-enumeration composition makes the canonical graph restrictions equal. Its arrow is the same retained innermost arrow. Its value on both routes is the product of the outer value, all intermediate values and all innermost values; associativity and commutativity of M identify those products. These equalities prove the actual `Calc` laws with the specified occurrence reindexing, not only a tree fold law. The bound is closed because every inner graph is an induced restriction and the outer graph never changes; arity and tree depth are unbounded.

Define the primitive assignment lambda:S.Assignment F by the indicated binary or nullary cut of value 1, and by the unary identity cut of value m for D(W,m). Its profile is exactly S.input and its output exactly S.result, so it inhabits the actual `Signature.Assignment` type. Evaluation of every template pair is equal: R flattens the same three blocks/arrows, units remove only a nullary empty/id block, and decoration equations use the commutative monoid laws. Thus a_lambda=(lambda,satisfaction) is a `Presentation.Model E_G F`.

`Tree.extend F lambda` is the actual A2 free strict extension. Its operation map equals THEOREM.md's recursive evaluation: both send leaves to the target identity and a node to its assigned cut composed with the recursively evaluated children, so induction on `Tree` identifies them. In particular its preservation of `Tree.substituteOperation` is the public `Tree.interpretFiber_substituteOperation` theorem applied to the target just constructed.

## 5. Completeness and generation for this actual declaration set

THEOREM.md proves termination of ->, characterizes every irreducible as the uniquely labelled right comb N(w), and proves `eval(N(w))=w` for every full flat witness w. The construction includes the zero-frontier decorated u_A case and the one-frontier identity-leaf case. For n>=2 it uses the first block and union of the remaining blocks, retaining the actual induced graph and the composite of the remaining arrow string. It therefore generates every independently defined F-operation without assuming that leaves reconstruct the whole.

By (3.1), the normalizing rewrite path is a `Presentation.Derives S E_G` derivation. Conversely `Presentation.sound E_G F lambda` proves that every D-derivation has equal evaluation. Therefore, for arbitrary raw t,u with the same output component, not only a preselected common arity,

    D(t,u) iff eval(t)=eval(u) iff N(eval(t))=N(eval(u)).           (5.1)

If evaluations agree, their retained profiles agree; transport both operations into that same full path fibre before using the normal-form argument. There is no illegal equation between different profiles. If profiles differ, all three conditions are false. Equal input graph lists without the ordered partition, whole graph or arrow string do not imply any condition in (5.1).

## 6. Isomorphism with `Presentation.quotient E_G`

Let Q be the already implemented `Presentation.quotient E_G`, let pi=`Presentation.projection E_G`, and define

    Phi = Presentation.extend E_G F (lambda, satisfaction).

This is the inverse direction of `Presentation.homEquiv E_G F` applied to the explicit model, not a newly postulated factor. The checked identity `Presentation.projection_extend` gives

    pi.comp Phi = Tree.extend F lambda.                         (6.1)

Hence Phi(pi(t))=eval(t). `Presentation.quotient_eq_iff` and (5.1) show that Phi is injective on every output component and every full profile fibre: equal Phi-images of representatives imply equal evaluations, hence D, hence equal quotient classes. Every quotient element has an actual representative; when a fibre p is prescribed, the actual quotient's `representativeOperation`/`projection_onOperation_surjective` supplies a representative in THAT p, not merely one of matching endpoints.

Define Psi on a full witness w by Psi(w)=pi(N(w)). This preserves its profile. Equation eval(N(w))=w gives Phi(Psi(w))=w. Conversely, for q=pi(t), the normalizing D-derivation gives Psi(Phi(q))=pi(N(eval(t)))=pi(t)=q. These establish two inverse maps on actual operations, including zero-arity fibres, not only a surjectivity claim or an abstract cardinality argument.

Phi is strict by `Presentation.extend`. Psi is strict as follows. It preserves identities and any simultaneous substitution because applying the injective strict map Phi to the proposed two sides gives respectively the same target identity or the same flat substitution w[v_i]. Every v_i retains its individual replacement profile q_i; the equality takes place in `Path.expand p q`. This proves Psi's identity and substitution preservation and yields an isomorphism of the actual `Calc` structures, with inverse strict maps Phi and Psi.

Explicitly, for ALL p,q and all quotient operations q_0 in Q.Operation(c,p), q_i in Q.Operation(componentAt(p,i),q(i)),

    Phi.onOperation(Q.substitute q_0 q q_i)
      = F.substitute(Phi.onOperation q_0) q (i |-> Phi.onOperation q_i).   (6.2)

The inverse equation holds for Psi. This uses the implemented quotient substitution, which `ParallelCongruence.quotient_substitute_eq` identifies with its representative construction. The result is independent of representative choices by `quotientSubstitute_project` and `projection_substitute_eq_of_rel`; no normalization hypothesis was smuggled into the generic quotient.

Thus the local effective decision procedure really decides equality in `Presentation.quotient E_G`, although that generic quotient implementation itself uses noncomputable representative selection. Nothing here claims that arbitrary E has decidable equality.

## 7. Universal-property and all-model checks

Under `Presentation.homEquiv E_G F`, Phi restricts back to the same explicit generator assignment lambda by `restrict_extend`. `extend_unique` makes it the unique strict factor satisfying (6.1), among all strict quotient maps, not only recursively defined functions.

For any fixed-base strict calculus map k:F -> T, the actual theorem `Presentation.extend_natural` gives

    Phi.comp k = Presentation.extend E_G T (postcomposeModel E_G a_lambda k).

This is target naturality in the public API's fixed quiver. Changing K or the component quiver is not silently treated as an instance of this theorem; the separately stated parameter/relabeling comparisons in THEOREM.md §8 require their explicit base maps.

`Presentation.derives_iff_all_models` then agrees with (5.1). For THIS presentation, equality in F, equality in Q, derivability, and equality in every model in the theorem's stated universe coincide. Equality in F has this separating force only because completeness was proved here; it was not used to define E_G or `Derives`. The general all-model result and its universe condition are unchanged.

## 8. Exact relationship to the checked located representative

Specialize N=6, K to the three-object chain and M to Z/3Z. In the Lean representative, fix an ambient simple graph G on Fin 6 and an arbitrary support S, including empty. A general graph with at most six vertices is represented by embedding its ordered vertex set as an initial segment and extending by isolated vertices outside S. This embedding is a coordinate choice, not a change in component equality.

`LOCATED_SYNTAX_COMPARISON.md` gives explicit maps L from raw trees on S(6,K,M) with whole G|S into valid located terms and B back to raw trees. At a raw cut, L composes the current root embedding with each declared cut inclusion. At a located cut, B computes each child's descendant-support union, uses the parent's retained induced graph, and labels the binary generator by the corresponding rank subsets and the stored intermediate interface. Nullaries, leaves and decorators are treated separately. The increasing-restriction identities prove both round trips by structural induction; child-slot functions agree pointwise on their actual zero/one/two slot types. No whole graph is inferred from isolated pieces.

The code's `GraphCoordinates.enumerate_eq_sort` identifies its executable increasing enumeration with the declared convention. `recover_rankBlock` and `rankBlock_injective` prove that canonical coordinates recover every included block. `graphCode` stores vertex count and the COMPLETE row-major adjacency matrix, so it is a faithful code of the standardized graph: each adjacency bit is recovered at position i*n+j. Since K is a chain, an arrow is uniquely determined by its stored ordered endpoints; the typed `Spine` consequently retains the entire K-arrow string. General K in §§1–7 still retains actual arrow values, not endpoints alone.

Under L and B, every valid instance of each raw schema is the identically named rule in `TypedNormalizer.E`, and conversely. The reverse implication is not obstructed by the generic located E being defined on all terms: E.sound preserves the full typed frontier, hence `valid_congr` keeps every intermediate term in a derivation valid whenever its starting term is valid. Every such intermediate cut is a genuine cut by `valid_cut_parts`. Context/equivalence closure therefore maps in both directions, and §3 handles the substitution closure in the actual `Presentation.Derives`. We obtain

    Presentation.Derives S E_G t u iff TypedNormalizer.E (L t) (L u).   (8.1)

Different disjoint supports with equal standardized graph/arrow colour remain different occurrence embeddings, not different component types. The formal theorem `repeated_component` explicitly exhibits that equality for two nonempty two-vertex blocks. The full `equiv_iff_standard_cut_eq` result proves equality reflection after standardization, so (8.1) is not an over-refined equality that silently keeps ambient location as a new colour.

Finally, occurrence substitution commutes with L and B: the raw route composes increasing inclusions e i_U i_V; the located route lifts the same descendant blocks to the root. Both enumerate the same ordered pairs of original and inserted occurrences. The actual checked finite-forest bridge is the COMPLETE chain `Term.allLeaves_iff_entries` -> `frontierDispatch_valid` -> `valid_frontierForest_graft`, together with `frontierDispatch_at`; the latter recovery-at-index theorem alone was insufficient and is not used alone. Thus every independently specified finite frontier forest, including repeated/empty components and different arities at different occurrences, is covered. This ties the substantive L instance to the very substitution and full witness data used by the general P theorem.

The maps in this section are a complete P comparison with actual public types; no public Lean adapter for L and B is claimed. A4 permits P for this general comparison. The already supplied L representative is not weakened, and no optional extra adapter is made into an unapproved prerequisite.

## 9. Result and exact stopping boundary

The local result now supplied is: for every frozen N,K,M, the explicitly finite seven-template instance of the ACTUAL `Presentation.Equations` has a terminating/confluent mixed orientation; its actual generated quotient `Presentation.quotient E_G` is isomorphic, by explicit inverse strict maps, to the independently defined full flat-witness calculus; its equality is decided by the exhibited normal form; and the checked representative is related by explicit two-sided syntax, equation and occurrence-substitution maps.

This is local mathematical support for C5's semantic-presentation part. It does not construct B1/B2's categories, B3's raw-refinement categorical completion and mixed coherence, B4's recoverability classification, C5's full refinement/transport package, or F2's all-degree bridge/use. The conditional semantic-refinement transfer in THEOREM.md remains conditional. Under the existing contract's conjunctive bundle/use gates, A4 remains OPEN for full scientific acceptance even when this local result is marked LOCAL_VERIFIED by independent review. No further B/F execution or amendment is authorized by this comparison.
