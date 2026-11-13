# C1 frozen target candidate — pre-attempt specification

Date: 2026-10-24. Contract: CompletionContract.md v0.1, unchanged,
SHA-256 47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e.
Authorization: C1 local graph-model milestone and Gate 1 assessment ONLY. No
C2/C3/C5/F2, B3/B4, equipment, or later bridge result is attempted or accepted.
Dependencies: accepted A1–A3; accepted B1–B2 used only in the Gate 1 comparison.
Branch: M, positive only. Obstruction would be a defect, not completion.
Status: SPECIFICATION SUBMITTED; proof implementation waits for parent release.

## Complete contractual C1 acceptance clause (unchanged)

**Class and claim:** M. Build a model family that simultaneously exhibits nontrivial interfaces, repeated occurrences, nonreconstructive cuts, and competing refinement trees.

**Inputs:** A1–A3. Use finite simple graphs with explicitly ordered vertices, a bound N≥6, and a finite category with at least three objects and nonidentity composable arrows. A three-object chain is an admissible starting case.

**Artifact:** Component types pair a graph with an arrow A→B. An n-ary witness consists of a whole graph, an ordered partition of its vertices into n possibly empty blocks, and a composable interface-arrow string whose composite is the whole arrow; the input components are the induced subgraphs with the relevant arrows. Restrictions use a declared canonical relabeling convention. Substitution refines the partition inside each block. Explain explicitly why the bound is closed under this operation.

**Discharge:** P for the family and all calculus laws; L for a typed nontrivial fragment; C for the finite test instance. The report must identify exactly which data are stored in a witness, in a whole, and in a leaf. It must not erase the whole graph while relying on it in the proof.

**Tests:** A mixed-interface four-leaf path containing two identical loop-arrow component types at the middle interface, refined differently; two binary groupings evaluating to the same flat cut; and two different whole graphs with the same ordered induced leaf graphs because a cross-block edge differs. Empty blocks test units, not the principal nontriviality condition.

**Dependencies:** A1, A2, A3. **Contract status:** OPEN.

**Minimum passing floor:** Uniform laws for arbitrary finite sizes, a declared closed bounded instance, the six-vertex repeated-nonempty-component certificate, and its use in C5/F2 are required. A one-off graph, empty middle blocks, or a tree-size truncation not closed under composition does not pass.

## Quantified target and conventions

1. For every small category K (in particular every finite category), every finite
ordered simple undirected graph G on [m]={0,...,m−1}, every arrow h:A→B, and every
n≥0, define the n-ary witness fibre over whole (G,h) as ordered partitions
(B₀,...,Bₙ₋₁) of [m] together with a composable K-arrow string
A=A₀→A₁→...→Aₙ=B of composite h. Empty blocks are allowed. Whole equality is
literal equality of m, adjacency, and typed arrow; not graph isomorphism.
Block order need not agree with vertex order. Within each block, vertices are
in increasing inherited order. The unique increasing enumeration
ε_B:[|B|]→[m] relabels its induced graph to [|B|]. Leaves contain only this
relabelled graph and their typed arrow, not ε_B or the other blocks.
Witnesses retain the whole, ordered actual vertex blocks, and full typed arrow
string. Output-indexing may store the whole in the index rather than duplicate
it, but it is never erased from the total witness carrier.

2. For every witness and every occurrence-indexed family of witnesses over its
exact input components, define substitution by the lexicographically ordered
blocks ε_Bᵢ(Cᵢⱼ) and concatenated arrow strings. Prove disjointness, exhaustivity,
canonical-relabelled induced-subgraph compatibility, the composite-arrow law,
profile law, identity/right unit/left unit, and arbitrary two-layer
associativity, at equality of FULL cut witnesses with canonical profile
transports. Do not prove just equality of leaf lists. Identity has the single
block [m] and arrow h. A nullary witness exists exactly for m=0 and h=id_A
(with A=B); an empty graph of nonidentity loop grade has no nullary witness.
There is no claim that all loop components are units.

3. The restriction coherence lemma is explicit: for C⊆[|B|],
ε_(ε_B(C)) = ε_B ∘ ε_C under the common domain [|C|], and
(G|B)|C = G|ε_B(C) literally after canonical relabeling. Its iteration supplies
strict graph-side associativity, not an unnamed isomorphism.

4. For every N∈N, restricting the component universe to graph size ≤N is closed
under identities and substitution of all arities: every block/refined block
has size ≤m≤N and substitution keeps the same whole. N bounds vertices, NOT
arity, tree size, depth, number of empty blocks, or category path length.
For each fixed arity and finite K there are finitely many bounded witnesses;
unbounded arities remain permitted. The principal finite instance is N=6 and
the category 0≤1≤2 (unique arrow a→b iff a≤b).

5. Define the actual path-profile nonsymmetric multicategory of these witnesses
on components (G,h); prove all laws in (2). Give its explicit comparison to
A1's Calc/Operation, the A2 evaluation supplied by primitive cut assignments,
and A3 soundness for specified parallel equalities used in the certificate.
No completeness, C5 presentation theorem, arbitrary-equation soundness, or F2
simplicial/2-Segal statement is claimed. The graph operation is not defined as
a tree or as a quotient by all model equalities merely to inherit a Calc.

## Mandatory concrete certificate (frozen before computation)

Whole vertices [6]; base edge set
{(0,1),(1,2),(1,3),(2,4),(3,4),(4,5)}.
Ordered four blocks ({0},{1,3},{2,4},{5}); interface path
0→1→1→1→2, grades the unique arrows. Both middle components are literally the
two-vertex one-edge graph with grade id₁, and both are NONEMPTY.
Refine occurrence 1 by local blocks ({0},{1}), occurrence 2 by
({1},{0}); both are binary cuts of that identical component but are different
retained witnesses. Outer occurrences use identities. The final ordered
ambient blocks are ({0},{1},{3},{4},{2},{5}). This is not permission to swap
occurrences: the inner partition order is supplied witness data.
Compare binary trees ((B₀ B₁)(B₂ B₃)) and (B₀(B₁(B₂ B₃))), using canonical
restrictions of the SAME retained whole, and verify equal FULL flat cuts.
Use the second whole obtained by adding the cross-block edge (0,5). Verify
its ordered induced leaves and interface path equal those of the base whole,
while wholes and total witnesses remain different. This is C1's required
nonreconstruction certificate only, not discharge of C3's arbitrary fibre theorem.
Boundary tests include empty blocks, an empty whole with a nullary identity
grade, and rejected invalid partitions/interface strings/nullary grades.

## Evidence requirements and anti-shortcuts

P: complete parameterized model/law proof, with all quantifiers and canonical
relabeling and interface composites visible. L: kernel-checked graph-specific
induction/restriction/substitution fragment plus actual mixed-interface typed
cut/tree data connected to the accepted A representation; formal objects must
retain real graph/partition data. A purely untyped graph table or unrelated A
import is insufficient. The precise L/P boundary must be itemized; full
all-size graph Calc Lean formalization is not demanded by §13, but a complete
mathematical Calc is demanded above. C: finite certificates computed by an
implementation independently checked by a separate implementation/reviewer;
finite domains, mutation-sensitive controls, source hashes and logs disclosed.
Use ordinary kernel proof, not native_decide as an undisclosed oracle.

Cheapest nonpassing solutions: a terminal/category-only calculus carrying
irrelevant graph tags; one six-vertex table with no uniform law proof; abstract
tree free calculus renamed as graph semantics; empty middle components;
identical leaves conflated with equal cuts; no canonical relabeling map;
strictly bounded arity/tree size destroying closure; skipping nullary grade
condition; quotient-by-all-observed-equalities claiming C5; or declaring C1
fully accepted while later C5/F2 uses are absent. Each is excluded by the
acceptance clause and quantified targets above. Restriction-species graph cuts
and standard multicategory machinery are reused baseline infrastructure,
not a new mathematical invention.

## Gate 1 decision boundary

After independent verification, assess whether accepted A1–A3 and basic B1–B2
support these real graph examples and their interpretation/parallel quotient
connections. Record CONTINUE, REPAIR, AMENDMENT NEEDED, or STOP with cited
artifacts. A compiling graph/table alone does not pass. C1 remains OPEN in its
full contractual status, with at most LOCAL_VERIFIED for this authorized
model milestone; required C5/F2 use and all later integrated gates stay OPEN.
No author-local success promotes itself to accepted.

## Pre-review clarification: exact L/P and C boundary

The empty graph with identity grade is an ordinary component; its identity tree
is one leaf occurrence. It is NOT the empty path or a nullary witness.

Planned new Lean namespace `WitnessedDecompositions.GraphCut`:
- `OrderedGraph`, `restrict`, `restrict_trans`: actual finite simple adjacency
  data and restriction along ordered vertex embeddings; the generic composition
  lemma proves equality of restricted adjacency, not just a numerical invariant.
- `CutSignature` / `cutSignature`: a genuinely graph-valued signature whose
  generators carry their whole, canonical block locations and typed interface
  arrow path; argument colours are standardized induced graph/arrow pairs.
- `graphEvaluate`: evaluation of these actual A `Tree`s to retained full flat
  cut data (whole + ordered ambient blocks + typed path), not leaf-list-only
  evaluation. The formal fragment may use the finite three-object chain; the
  arbitrary finite nonthin-category theorem is P and retains actual arrows.
- `mixed_four_frontier`, `repeated_nonempty_component`,
  `repeated_refinements_distinct`, `occurrencewise_refinement_certificate`,
  `competing_groupings_same_cut`, `competing_groupings_distinct_trees`,
  `cross_edge_same_leaves`, `cross_edge_distinct_wholes`: kernel certificates
  of the frozen example, including actual typed A `Tree`/occurrence grafting
  (or its accepted free operation API) and graph-valued evaluation.
The precise declaration names may be changed without changing their statements;
any implementation-only naming change is recorded in the theorem index. The
full all-parameter graph Calc and all arbitrary-cut unit/associativity laws are
P, not claimed L. The fragment's evaluated trees must be shown to agree with
the P calculus via a written explicit comparison, not an unsupported claim
that any imported tree syntax automatically is the semantic model. Formal
verification may be stronger than this boundary, but will not replace it with
an untyped or graph-erasing fragment.

The C finite law suite is frozen to all simple graphs on m=0,1,2,3 vertices,
all ordered partitions into n=0,1,2,3 blocks (including empty blocks), and all
weakly increasing interface strings in {0,1,2} of length n+1. Test canonical
restriction, identities, well-formedness, and every single-block refinement
into 0,1,2 blocks. For associativity use every nested three-stage vertex-label
assignment with each local arity in {0,1,2} on m≤3, with full whole retention;
redundant vertex-label and sorted-block implementations compare flat results.
The six-vertex frozen certificate is checked separately; no exhaustive claim
for all six-vertex graphs is made. The all-size P proof, not this bounded C
suite, discharges arbitrary simultaneous substitution/associativity.
Required mutations: remove whole data (must fail cross-edge distinction),
collapse repeated occurrences by component type (must fail independent
refinement result), ignore canonical local-to-ambient relabeling (must fail
noncontiguous/opposite-order blocks), forget arrow values/typing (must reject
invalid composability or grade), and conflate empty identity leaf with nullary
(must fail arity/occurrence count). Invalid overlapping or missing-vertex
partitions must be rejected. Independently authored checker may use an
equivalent more efficient factorized enumeration only with documented proof
of coverage; it does not silently shrink the frozen domain.

The nullary negative controls explicitly include unequal endpoints. To test a
nonidentity loop without vacuity, the supplementary finite interface category
is [2]×C₂: objects {0,1,2}, arrows (a≤b,e) with e∈{0,1}, composition by endpoint
composition and addition modulo 2. The empty graph of grade (1≤1,1) has NO
nullary witness, while grade (1≤1,0) does. This is a C1 boundary test, not an
activation of C2. Existing graph/rewrite Lean declarations may be reused under
exact source hashes, rechecking and explicit A-model comparison rather than
duplicated; the stated fragment and all certificate content stay unchanged.
