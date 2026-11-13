# C1 local graph-model milestone: independent pre-attempt depth review

## Decision

**CLEAR TO ATTEMPT, subject to parent release.** The exact target below meets
§3.4's intended depth for the authorized **local C1 model milestone**. This is
neither proof verification nor acceptance of C1, Gate 1, or any later result.
There is no unresolved pre-attempt scope defect and no material amendment.

- Reviewer: `/root/review_graph_cut_target_depth`, a non-author of the target and
  implementation. Review performed 2026-10-24, before proof-attempt release.
- Lead: `/root/construct_typed_graph_cut_model`.
- Contract: v0.1, SHA-256
  `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
- Reviewed target: `research/workstream_C1/C1_Targets.md`, SHA-256
  `7a5d4bb8dd3aa0715c82b73b8c169def2935b98f41addfd0eaaf03a606be244e`.
- New working tree:
  `/workspace/shared/witnessed_C1_20261024/witnessed_decompositions`.
- Read-only baseline inspected:
  `/workspace/shared/witnessed_B_20261024/witnessed_decompositions`.
- Authorization: the parent supplied the user's express C1 milestone approval,
  “Yes, let's do it.” This permits the bounded C1 local model and Gate 1
  assessment, not automatic execution of C2/C3/C5/F2, B3/B4, or later work.
- Branch: **M, positive only**. An obstruction is a defect to report, not an
  alternate passing outcome. Full C1 remains **OPEN**; at most LOCAL_VERIFIED
  can be earned here after independent verification. C5/F2 use remains OPEN.

This review read the full C1 clause, §3, Gate 1, and §13, together with the
relevant frozen-core conventions and C5/F2 integration clauses. The complete
C1 acceptance clause is preserved verbatim in substance in the reviewed target;
its downstream-use floor has not been deleted. Review also inspected actual A
`Collection`/`Calc` APIs and A4 graph/test/comparison sources, not only summaries.
No proof or implementation file was changed by this reviewer. This report and
its input manifest are the only new reviewer artifacts.

## Cheapest technically compliant route and intended mathematical depth

The cheapest legitimate route is to reuse the existing A4 flat graph-cut
construction specialized to the trivial decoration monoid, extract and verify
its uniform restriction/substitution arguments as the C1 model, connect its
precise retained data to the accepted A APIs, reuse kernel graph/coordinate
lemmas where applicable, and add or reuse enough genuinely graph-specific typed
certificates to cover the frozen C1 example and its independent occurrence
refinements. A fresh C1 finite checker and a separately authored/redundant
implementation then check the stated finite domain and mutations. There is no
requirement to duplicate correct proofs or inflate line counts.

**Would this cheapest route satisfy the intended goal? Yes, for this local
model milestone only, provided every frozen condition below is met.** It is a
substantive test of the foundational representation using actual graph cuts,
canonical coordinate transport, repeated equal colours, distinct whole graphs,
and nontrivial mixed interfaces. It is not a new discovery of graph restriction
species or multicategory laws. It does not supply the semantic-presentation,
refinement-transport, or all-degree 2-Segal integration required for full C1 and
its scientific bundles. Reuse must be attributed and independently verified;
old artifact status does not automatically discharge a new obligation.

A cheaper-looking route—renaming the existing graph-code checks or simply
multiplying a category example by inert graph tags—would not establish the
model laws or A comparison. The target excludes it by requiring an independently
defined full-witness calculus, full equality laws, actual typed graph/tree data,
and an explicit comparison with the mathematical graph calculus. Successful
compilation or a one-off six-vertex computation alone cannot pass.

## Frozen mathematical inputs and assumptions

The target is frozen before computation as follows; these are conjunctive.

1. **Parameters and equality.** Uniform P statements cover every finite ordered
   simple undirected graph on `[m]` and every finite interface category, with
   actual morphisms and full composable strings retained. The target offers the
   harmless stronger quantifier over small categories. Graph equality is literal
   vertex-count/adjacency equality, not unlabelled isomorphism. A component is
   precisely graph plus typed arrow; ambient location is not part of its colour.
2. **Witness data.** A witness retains the whole graph and arrow, the full ordered
   partition into possibly empty blocks, and the complete interface-arrow
   string with its composite equation. Whole storage in an output index is
   allowed only because it remains in the total carrier and comparison. A leaf
   has its canonically relabelled induced graph and arrow, not its embedding.
   Equality of leaves alone is not equality of cuts, partitions, or wholes.
3. **Canonical coordinates.** Within each block use the increasing enumeration
   `epsilon_B`; block order itself is arbitrary supplied data. Prove
   `epsilon_(epsilon_B(C)) = epsilon_B composed with epsilon_C` and literal
   equality of the corresponding twice-restricted ordered graphs. This must
   account for noncontiguous blocks, empty blocks, and iterated restriction.
4. **Operations and occurrence linearity.** An inner witness must have exactly
   the graph/arrow colour of the outer occurrence being replaced. Substitution
   lifts inner blocks through that occurrence's increasing inclusion and
   concatenates inner arrow strings in lexicographic occurrence order. Prove
   disjointness, coverage, canonical induced-subgraph compatibility, composite
   arrow preservation, the full profile law, both units, and arbitrary two-layer
   associativity of full witnesses with the actual profile transports. A family
   is indexed by occurrences, never looked up by component equality.
5. **Identity and nullary cases.** The identity on any component has one whole
   block and one arrow. A nullary witness exists exactly at empty graph with
   identity arrow and equal endpoints. An empty identity-colour external leaf
   remains one occurrence, distinct from the zero-leaf nullary. Empty graph with
   nonidentity loop arrow and unequal-endpoint empty graph have no nullary.
6. **Closed bound.** For every `N`, graph size at most `N` is closed because the
   whole is unchanged and every inner graph is an induced restriction. No bound
   on arity, path length, tree size, depth, or empty-block count is imposed.
   Each fixed arity in a finite category is finite, not the entire unbounded
   operation carrier. The principal bounded instance is `N=6` and `0<=1<=2`.
7. **A comparison.** Define graph cuts independently of trees/semantic quotient
   shortcuts, construct the P-level path-profile nonsymmetric multicategory,
   give its explicit A1 `Calc`/`Operation` comparison, the A2 primitive assignment
   and evaluation, and A3 soundness of the specified parallel certificate
   equalities. A general C5 completeness theorem is not imported as an assumption
   or claimed as newly discharged. No model quotient by all observed equalities
   may replace the generated-equation distinction.

## Frozen principal certificate and finite evidence

The six-vertex whole has edges
`{(0,1),(1,2),(1,3),(2,4),(3,4),(4,5)}` and ordered blocks
`({0},{1,3},{2,4},{5})`, with interface path `0->1->1->1->2`.
Both middle components are literally the same nonempty one-edge two-vertex graph
with arrow `id_1`, despite different ambient locations.

Both occurrences receive proper binary refinements: the first uses local blocks
`({0},{1})`, the second `({1},{0})`. Outer occurrences receive identities. The
result must retain ambient order `({0},{1},{3},{4},{2},{5})`. This is a supplied
choice of two independent inner cuts, not an exchange rule on the outer profile.
The certificate must demonstrate distinct inner witnesses and correct independent
A occurrence dispatch, not merely different decoration values.

The binary trees `((B0 B1)(B2 B3))` and `(B0(B1(B2 B3)))` must remain distinct
presentations but evaluate to the same **full flat cut** with their declared
canonical internal restrictions. Adding the cross-block edge `(0,5)` yields a
second retained whole with the same ordered leaf graphs and arrow path, but a
different whole and total witness. This is the required C1 nonreconstruction
example, not C3's arbitrary fibre theorem or a failure of 2-Segality.

The C domain is frozen to all simple graphs of sizes `0,1,2,3`, all partitions
into `0,1,2,3` ordered blocks, and all weakly increasing three-object interface
strings of the appropriate length. It checks canonical restriction, identities,
well-formedness, and every single-block refinement into `0,1,2` blocks. The
associativity test uses every nested three-stage vertex-label assignment with
each local arity in `{0,1,2}` for sizes at most three, retaining the whole. The
six-vertex certificate is separate: there is no claim of enumerating every graph
on six vertices. Any equivalent factorized enumeration needs a coverage proof,
not just matching counts on a subset. Finite tests never replace uniform P laws.

The supplementary finite category `[2] x C2` has arrows `(a<=b,e)`, `e` modulo
two. At the empty graph, `(1<=1,1)` is a valid nonidentity loop arrow but has no
nullary witness; `(1<=1,0)` does. This avoids a vacuous nonidentity-loop test in
the thin principal chain. Unequal-endpoint nullaries are also rejected.

Required mutation/negative controls are:

- erasing the whole must destroy cross-edge distinction;
- collapsing occurrences by identical component type must break the independent
  refinement result;
- omitting local-to-ambient canonical relabeling must break the noncontiguous or
  opposite-order example;
- forgetting actual arrows/typing must be detected by composability/grade checks;
- conflating an empty identity leaf with nullary must break arity/occurrence count;
- overlapping or incomplete partitions must be rejected.

## Frozen evidence and acceptance boundary

**P:** Complete parameterized model and all calculus-law proofs, including the
canonical restriction identities and explicit A comparison. No central gap may
be supplied by a successful computation. The all-category and arbitrary
simultaneous-substitution claims remain P even when the L representative is
smaller. Report every hypothesis and quantifier.

**L:** A real graph-specific typed fragment, not an unrelated imported A module.
The planned statements (names may change without weakening them) are
`OrderedGraph`, `restrict`, `restrict_trans`, `CutSignature`/`cutSignature`, and
`graphEvaluate` retaining whole, partition and typed path; plus
`mixed_four_frontier`, `repeated_nonempty_component`,
`repeated_refinements_distinct`, `occurrencewise_refinement_certificate`,
`competing_groupings_same_cut`, `competing_groupings_distinct_trees`,
`cross_edge_same_leaves`, and `cross_edge_distinct_wholes`.
These concern actual typed A trees/occurrence grafting or the accepted free
operation API, with explicit agreement between graph-valued evaluation and the
P calculus. Full all-size graph `Calc` Lean formalization is not required by
§13, but the fragment cannot be replaced by graph-erasing data. Reused
statements must have exact hashes and be rechecked. Final evidence must give
exact declarations, theorem statements, dependency closure, source/build hashes,
and axiom reports; native computation is not silently kernel proof.

**C:** Execute the frozen finite suite with separately authored/redundant
checking, record domains and coverage, retain source hashes and logs, and show
that the specified mutations are detected. The vertex-label and sorted-block
implementations compare full results. Distinguish author-run evidence from
independent reproduction and disclose shared-model review limitations.

**Gate 1:** Only after mathematical and reproducibility review, determine whether
accepted A1–A3 and basic B1–B2 support these actual graph examples, evaluation,
and parallel quotient connections. Record CONTINUE / REPAIR / AMENDMENT NEEDED /
STOP with artifact citations. This review does not yet make that decision.

**Status discipline:** C1 full status remains OPEN, with at most LOCAL_VERIFIED
for this milestone. Required C5/F2 use and all integrated scientific-scope gates
remain OPEN; C2/C3/C5/F2, B3/B4, and equipment are not activated. No build log,
number of tests, old accepted theorem, or author assertion can change that.

## Shortcut-to-excluding-clause audit

| Tempting shortcut | Why it does not pass; excluding clause |
| --- | --- |
| One selected graph/table only | C1 minimum floor and target quantified items 1–4 require uniform finite-size/category laws. |
| Terminal or category-only calculus with graph tags | Target item 5 independently defines actual graph operations; L boundary requires graph-valued typed evaluation. |
| Rename the free tree calculus as flat cuts | Target item 5 and L/P comparison require independently defined full semantic witnesses. |
| Empty middle blocks as repeated components | C1 tests/floor and frozen six-vertex certificate require two equal NONEMPTY K2/id1 colours. |
| Refine equal colours identically by dictionary lookup | Target item 2, opposite proper binary refinements, and occurrence-collapse mutation require independent indexed families. |
| Treat ambient subsets as new colours | Target item 1 makes colours induced graph plus arrow; equal-colour certificate must prove literal equality. |
| Retain only isolated leaves but use whole edges in proof | Target items 1–2 require retained whole/partition data and full witness equality; whole-erasure mutation detects it. |
| Store only arrow endpoints in arbitrary finite categories | Target items 1–2 retain actual arrows; supplementary nonidentity loop grade tests the boundary. |
| Canonical labels only up to an unnamed isomorphism | Target item 3 requires the explicit strict increasing-enumeration compatibility equation. |
| Bound syntax depth/arity to make everything finite | Target item 4 explicitly forbids this; all arities and empty-block counts remain possible. |
| Make every empty or loop component nullary | Target item 2 and clarified L/P/C boundary require empty graph AND identity arrow AND equal endpoints. |
| Collapse empty identity leaf with nullary | Clarified boundary and required arity mutation preserve the one-versus-zero occurrence distinction. |
| Prove equality of frontiers only for groupings | Target item 2 and grouping certificate require equality of FULL retained flat witnesses, while raw trees differ. |
| Call cross-edge loss a 2-Segal obstruction | Contract §3.3 and target scope prohibit it; no simplicial comparison is attempted. |
| Re-run old A4 tests and claim C1 accepted | §3.3–§3.4 and C1 downstream-use floor require fresh bound evidence and keep full C1/C5/F2 OPEN. |
| Replace P with a bounded exhaustive check | C1 P/L/C discharge split and target finite-domain caveat explicitly prohibit it. |

## Pre-attempt issues and disposition

The initial draft was hash
`2aa5e3d04bf5d0c9e45f6e0a3b334d3b32b5a0f7c7d00a2683e5f7ebcbf2bb6d`.
It already satisfied the substantive breadth and retained-data requirements.
Before clearance, this reviewer requested explicit empty-identity-leaf versus
nullary separation, unequal-endpoint rejection, a frozen finite C domain, and a
nonvacuous category for the nonidentity-loop boundary. The final reviewed hash
adds all of these and the named L/P boundary. These are clarifications enforcing
the existing contract, not changes to an observed failed theorem or material
scope amendments. No proof attempt was cleared at the earlier draft hash.

The old A4 code already includes canonical coordinates, actual graph data, a
six-vertex repeated nonempty component, and cross-edge separation. Its Python
checker has redundant recursive/address evaluations and reports 52,147 critical
instantiations through two vertices. Those are relevant reuse context only:
this reviewer did not rerun or independently certify those historical numbers
in this pre-attempt review, and they do not replace the new C1 domain. The old
A3 local comparison supplies a useful explicit `FlatCut`/A API template; its
existence is not itself a new C1 acceptance decision.

## Assurance and stopping condition

Correctness verdict now: **target internally coherent; proofs not yet reviewed**.
Scientific-depth verdict now: **PASS for the authorized local target**, not full
C1 or the program's integrated significance. Source provenance and dependency
status were inspected, but this is an agent-managed non-author review with
correlated-model limitations, not external human certification.

The pre-attempt task ends with this hash-bound clearance and evidence inventory.
Any material weakening of the target requires renewed scope review and the
contract's amendment protocol. Equivalent implementation names and stronger
proofs do not. Final mathematical/reproducibility acceptance must inspect the
actual completed arguments, typed declarations, and fresh evidence separately.
