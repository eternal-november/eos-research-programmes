# F1/F3 candidate: recognition versus scalar quotient and actual refinement

Author candidate, 31 October 2026. **Not an acceptance claim.** This is a selected-class theorem and proof, with an explicitly bounded recognition category. It does not assert that every finite discrete 2-Segal set is a graph-cut object, or that arbitrary CUT outer cells have a simplicial nerve.

## 0. Exact obligation and scope

Original v0.1 F1 requires an exact interval-factorization criterion, units, coherent iteration, and C5/B3 connection. F3 permits a selected interface-typed recognition/comparison with explicit morphisms and inverse laws, but demands presentation-quotient/refinement compatibility on an unbounded family, a sharp boundary, and a positive model not supplied by single-valued composition. Neither clause demands fixed-endpoint lifting of every quotient refinement, generation of every finite span by the C5-only signature, or a simplicial object of arbitrary nonexact roots. Those are distinct stronger questions.

The theorem below treats the actual original seven-law C5 calculus and a natural unbounded graph-indexed scalar quotient family. It has a fully discrete positive side. Its reverse category is explicitly **marked graph-cut 2-Segal objects**, not arbitrary 2-Segal sets. The graph-restriction construction itself is established baseline. The original integrated A4/C5/B3 dossier already proves the unquotiented multiplication fibre and explicitly records scientific significance NOT ACCEPTED for scalar-product/coherence specialization; this draft does not reverse that verdict. The proposed increment is the compatibility classification and the exact refinement map, not a new invertible-operad correspondence.

## 1. Parameters, quotients, and operations

Fix N≥6, a nonempty finite category K (principal examples have ≥3 objects), and a finite commutative monoid M. All finite ordered graphs through N vertices occur. Profiles, arities, tree depths and histories are unbounded; taking all N and M gives an unbounded parameter family. Components are W=(G,f:A→B). An operation is a retained whole W, a composable full arrow string (f_1,...,f_n), an actual ordered partition (U_1,...,U_n) of V(G), including empty blocks, and m∈M. Input components are (G|U_i,f_i), and f=f_n...f_1. Its scalar is m. Nullaries exist precisely at (empty,id_A), with every scalar m. Substitution refines the actual subsets by increasing inclusions and multiplies all participating scalar values.

For each graph G choose a monoid congruence R_G on M with

    R_(G|U) ⊆ R_G

for every actual vertex subset U. Let C_G=M/R_G and j_HG:C_H→C_G for H=G|U. The quotient D_R retains all structural coordinates and replaces m by [m]_G. This is a substitution quotient: a changed child scalar is equivalent in the whole by the displayed inclusion, and multiplication is congruence compatible. Conversely unary decoration multiplication and binary cuts force these two conditions. This is the original-kernel classification source Lemma 2, not an assumed semantic equality presentation.

The relation is presented from original C5 by adding d_m^W=d_n^W for each m R_G n. This is a finite schema at fixed N,K,M. Soundness is the preceding congruence argument. Completeness follows by the original right-comb/root-decoration normal form: equal structural coordinates and equal scalar classes are related by the corresponding root equation. This statement is an object-presentation theorem; it does not assert an unproved coherent completion for arbitrary R.

## 2. Structural interval fibre theorem

Let w have n≥3 inputs and select a proper interval [i,j] of length between 2 and n−1. Let H=G|(U_i∪...∪U_j). Then the FULL original F1 factorization fibre, with intermediate component ranging over all original components, is canonically

    { (a,b) ∈ C_G × C_H : a·j_HG(b) = c },                 (2.1)

where c is the scalar class of w.

**Proof.** Equality of flattened actual partitions forces the selected outer block to be U=U_i∪...∪U_j. Thus the intermediate graph is H. Its grade must be f_j...f_i; endpoints are A_(i−1),A_j. The inner partition is the inverse image of (U_i,...,U_j) under the increasing inclusion of U, and all remaining outer blocks and grades are forced. Conversely those structural factors exist and substitute to the given structural witness by the induced-restriction identity. Only their scalar classes a,b are free, and substitution is exactly a·j_HG(b). Reading classes and equipping the forced structural factors are inverse maps. Cross edges remain in the retained G and H throughout. QED.

For fixed G,H the substitution map C_G×C_H→C_G is bijective **iff C_H is a singleton**. Sufficiency is immediate. For necessity, if b≠1 in C_H, the distinct pairs (j_HG(b),1) and (1,b) have the same image. This argument does not require injectivity of j_HG or cancellation.

### Recognition criterion

The following are equivalent:

1. Every proper nontrivial contiguous-interval factorization map of D_R is bijective.
2. Every C_H is a singleton, including H=empty.
3. D_R is canonically isomorphic to Cut(N,K,1), by forgetting its unique scalar class.
4. D_R has the full ordinary graph-cut interval-record realization described below, retaining exactly its operations (not merely a selected normalized subcalculus).

For (1)⇒(2), fix any H and use G=H with three blocks (V(H),empty,empty); choose the first two as interval and identity grades at any object of K. This is a proper length-two interval, including when H is empty. Its inner graph is H, so the previous test applies. This uses actual allowed empty occurrences, not a deleted occurrence. If one bans empty blocks, the statement must be altered near the graph bound and the nullary boundary is no longer tested this way.

For (2)⇒(3), erase the single scalar coordinate; the structural formulas and unit operations agree. (3)⇒(1) is (2.1). The remaining equivalence means the explicitly constructed operation-preserving comparison, not every imaginable nerve that discards witness data.

Unary operations in the positive case are only identities. Nullary operations are exactly the single designated unit at each (empty,id_A). Empty-interval insertion is at its named boundary and inserts that component and empty subset; it is not deletion of an arbitrary empty component. One-slot and whole-path factorization have the same forced structural form and unique scalar. Thus no boundary hypothesis is inferred from positive-arity tests alone.

## 3. Forward/reverse discrete construction and coherence

For the recognized quotient define Y_n to consist of G, its ordered n-block partition, and a composable n-arrow K-path. For n=0, G must be empty and Y_0=Ob K. Its full witness is the scalar-free operation with those data and whole grade the composite path. For any monotone α:[m]→[n], take the induced graph on the union of blocks α(0)+1 through α(m), group consecutive blocks between α(j−1) and α(j), retain boundary objects A_α(j), and compose the arrows along each such run. An empty run gives identity arrow and empty block. Standard increasing-coordinate restriction identifies these literally with the operation coordinates.

The induced-restriction identity and category associativity/units prove Y(β)Y(α)=Y(αβ) for every pair, including constant maps. A triangulation reconstructs its retained root graph and partition recursively: the root triangle supplies the whole and its two actual subsets, and the subtriangles partition the induced graphs inside those subsets. Concatenation through increasing inclusions gives the unique full partition and arrow string. No cross edge is reconstructed from isolated leaves. Thus every triangulation comparison is bijective. Degeneracy image is exactly a specified empty/id edge, proving unitality.

**Reverse.** For an object in the declared target category (below), an operation with n-input profile and output W is an n-simplex with those ordered principal edges and long edge. Substitute by gluing the supplied simplices into the corresponding consecutive runs: the triangulation bijection gives the unique combined simplex. Equivalently its partition is the explicit lifted concatenation above. The latter formula proves that different triangulation choices give the same actual witness, so associativity, identity, and genuine nullary substitution agree with C5. Forward then reverse reads precisely the original whole, ordered blocks and grades; reverse then forward reads the same simplex. The comparison laws are literal equalities in these coordinates.

**Morphisms and declared target category.** Source objects are recognized D_R with their graph/category markings. A source morphism is an actual base-changing calculus map that retains graph and ordered partition coordinates and whose colour-arrow action is independent of the graph: its value on (G,f) is (G,φ(f)), with one common map on interface objects. This is an independently checkable condition on a calculus map, not a requirement that it already arise from a functor. Nullary units at empty/id force φ(id_A)=id_φ(A). Binary empty-graph cuts with arbitrary composable f,g force φ(gf)=φ(g)φ(f). Thus φ is a functor F:K→K'. Preservation of profile colours forces the image of every operation to have exactly the F-image full grade string; retained partitions and the singleton scalar leave no further choice. Conversely every such F gives the required map. A bound inclusion N≤N' is necessary for these retained graph maps. Descriptions by different monoid maps h that induce the same actual quotient map are not distinct morphisms; forgotten presentations cannot be recovered.

Target objects are the marked Y(N,K) above. A target morphism is a simplicial map retaining the graph and every actual block coordinate, whose Y_1 grade action is independent of graph, with the induced Y_0 interface map. Degeneracies on empty graphs force identity preservation. The three edges of a two-simplex with empty graph and composable grade path (f,g) force φ(gf)=φ(g)φ(f). Hence its grade map is a functor F. Every n-simplex's principal edges then force the entire F-image path; graph/partition preservation fixes the remaining coordinates. Thus every target morphism is the explicit coordinate map induced by its recovered F. Conversely those coordinate maps are simplicial by the already proved formulas. These arguments prove actual bijections on the independently specified hom classes; they do not merely define both classes as parameter maps. Forward and reverse read the same F and are mutually inverse on hom sets. On source objects the reverse recovers the unique-scalar representative canonically isomorphic to D_R; it does not recover its prior M,R presentation.

This restricted category is intentional. Claiming all simplicial maps, or recovering M,R,h from Y alone, would be stronger and is not proved. This is a comparison on an explicitly parameterized family (as permitted by F3), not a reconstruction of all abstract graph-marked 2-Segal objects. The recognition result classifies which quotients in §1 enter it, rather than naming an arbitrary cut axiom equivalent to itself.

**Positive non-single-valued model.** Take a category with three interfaces and a composable A→B→C path. Two one-vertex input graphs admit wholes both with and without the edge joining their vertices; the input components and grades agree but the retained whole differs. Hence output composition from the two inputs is genuinely multivalued. For N≥6 choose six vertices split among nonempty blocks and nested four-leaf cuts, including repeated equal component types. Distinct trees and decoration placements give genuinely different presentations identified by the complete quotient.

## 4. Actual C5/B3 quotient and refinement compatibility

Write P_M for original C5 syntax with its seven equation families R,UL,UR,D0,DA,DL,DR, and Comp_M for the independently presented B3 category with its ordinary critical coherence O and mixed MOut/MIn relations. The original C5 theorem identifies P_M/E_M with D_M. The original B3 theorem gives Comp_M ≃ Ref(D_M) with complete original-slot tuple normal forms. At recognized R the added equations identify every root scalar; the resulting presented calculus is exactly P_1/E_1, by replacing every d_m by d_1 and using D0. Thus the independently specified comparison completion for this recognized quotient is **Comp_1**, not a quotient category defined by all true target equalities.

The map h:M→1 sends each raw d_m to raw d_1 (not prematurely to an edge), every binary cut to the same cut, and u_A to u_A. It maps all seven equation families to their target instances. The original parameter theorem checks every O, MOut and MIn relation and therefore defines a functor Comp_M→Comp_1 independently of semantic fullness. Its comparisons commute on actual arrows:

    P_1 ∘ Comp(h) = Ref(q) ∘ P_M.

Here Ref(q) sends (b_1,...,b_n) to (q(b_1),...,q(b_n)), retaining every original occurrence, each child profile, every length including zero, every ordered partition and grade. Only each child's scalar is forgotten. Composition commutes because the same occurrence splitting is used and q preserves substitution. Equality in the target is therefore exactly entrywise equality of those retained data, not equality of concatenated targets or aggregate scalar products.

Reverse on the quotient side takes an operation to the established right-comb normal form at scalar 1 and a refinement tuple to insertion of its entries' normal forms followed by normalization. Ordinary/mixed coherence proves the inverse comparison and naturality. For parameter maps F the normal section has the explicit comparison ν'(F N(w)); its cocycle law is equality of pure equation paths supplied by O coherence. These are the original INTEGRATION §5 equations, now connected to the discrete cut object rather than asserted anew.

Thus genuine witness identification in P_M is compatible with an independently specified B3 completion, even though fixed-endpoint lifting through D_M→D_1 can fail. Such lifting is not silently built into the definition of “compatibility.”

## 5. Sharp limits and CUT connection

**Fixed-endpoint lifting is stronger.** In the selected graph-indexed scalar family, the existing classification says universal fixed-endpoint refinement lifting holds iff R_empty is equality and all nonempty R_G are orbits by one subgroup H≤M×. Our recognition criterion requires R_empty total. Therefore full operation-preserving recognition and that stronger lifting coexist iff M is trivial. For nontrivial M the empty/id nullary operation of scalar m has no children; its unique empty forest cannot reach a different scalar n although the quotient identifies them. This is a sharp family-wide no-go with a positive M=1 repair, not an unexplained isolated counterexample. It does not make FL a new F3 requirement.

**Retaining full M is still possible as a module.** One may retain arbitrary outer scalar and normalize each proper inner factor to scalar 1. Then all induced inner cut data are forced and coherent under contractions, rotations and exact grafts. But this does not identify D_M with Y: Y does not recover its root scalar. Full reverse reconstruction needs retained M and the module/root data. CUT §5 identifies exact operations with its X through contractible full interval extensions; §6–8 constructs their actual rooted action on arbitrary quotient outer cells; §9 gives only ambient, generally noninvertible comparisons for arbitrary grafts; §10 gives actual unique-lift tests for interface transport, including the nullary diagonal. These are genuinely compatible scoped structures, not a simplicial nerve of every nonexact cell.

**Distinction from CUT's all-span signature.** The discrete M=1 original K-graph slice embeds fully faithfully in CUT X (§4). This connects the present recognized quotient to the original-profile slice of the actual exact construction without asserting that old C5 generates every finite span or map. The latter bridge is expressly unproved and sometimes impossible at horizontal level; it is not needed for this theorem.

## 6. Pinned dependencies and remaining review questions

Read the exact originals, not only copies in I1:

- `contract_revision_20261028/final_artifacts/Original_Completion_Contract_v0.1_VERBATIM.md`, F1/F3, C5 and B3.
- `contract_revision_20261028/extracted/witnessed_decompositions/research/workstream_A/rewrite/A3_LOCAL_COMPARISON.md`, original generators, seven laws, object normal form and semantic isomorphism.
- `contract_revision_20261028/extracted/witnessed_decompositions/research/workstream_integration/proof/Completion_Comparison.md`, independently specified B3 completion and ordinary/mixed coherence.
- Same directory `Semantics_Transport_Factorization.md`, §§2–5 actual tuples and parameter/morphism laws; §6 structural original fibres.
- `original_mixed_criterion_20261029/main/C5_Fixed_Endpoint_Kernel_Classification.md`, Lemma 2 and Theorem 3.
- `contract_revision_20261028/structural_extracted/proof/Global_Cut_Repair.md`, §§1–5 and §§6–11, exact-X versus rooted-module distinction.

All paths relative to `/workspace/shared`. SHA-256 pins are written separately in `theorem_candidate_dependencies.sha256`.

**Remaining gaps, not covered by this draft:**

1. Independent review must judge whether the selected-class classification plus original B3 integration meets F1/F3's scientific floor. The category of marked graph-cut objects is narrower than arbitrary finite discrete 2-Segal objects; no misleading general equivalence is claimed. An honest outcome may be technically correct comparison plus scientific-scope shortfall.
2. The standard graph-restriction 2-Segal construction and generic invertible-operad comparison need explicit primary-source literature comparison in the final disposition; this candidate adds no novelty claim for them.
3. Original F2 computational and selected Lean requirements are separate dependency gates; the all-degree mathematical proof does not replace them.
4. This theorem does not give a new coherent B3 completion for every nonrecognized graph-indexed congruence. Only recognized quotients are identified with Comp_1, while arbitrary R has the object presentation and sharp failed recognition test. A stronger arbitrary-R completion theorem must be separately proved if desired.
5. Coherence is constructed and forced here; a separate example of arbitrary chosen noncoherent cut data is not a missing premise in this family. Generic free calculi can lack factors; the original full F1 test suite remains an explicit residual obligation until the no-factorization, incompatible-choice and missing-unit controls are matched to source evidence or supplied.
6. No F1 amendment is needed for this theorem's use of the stated full proper-interval map. Replacing that map by marked/groupoidal normalized factors would require an explicit amendment before acceptance.
