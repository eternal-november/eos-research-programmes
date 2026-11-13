# Independent C1 Lean and semantic comparison audit

## Verdict

**PASS for the frozen local L fragment and its explicit P semantic adapter.**
The implementation is a genuinely graph-valued, mixed-interface instance of
the accepted A representation, not a graph table beside an unrelated imported
tree theorem. Fresh independent compilation, source inspection, axiom review,
and isolated type-rejection probes found no unresolved correctness defect.
One precision omission in the P adapter was repaired during review: its
all-tree induction now explicitly preserves the increasing order of every
block list, so the comparison is literal list equality, not only set equality.

**Scientific-depth verdict: PASS for the authorized local infrastructure
milestone, not a novelty or full-program verdict.** This evidence supports
CONTINUE at Gate 1 when combined with the separate full P/C reviews and the
accepted A1–A3/B1–B2 dependencies. This review does not alone approve the
aggregate gate. Full C1, its required C5/F2 uses, and later integrated claims
remain **OPEN**. The branch is M, positive only; no obstruction is counted as
completion.

Reviewer: `/root/audit_graph_cut_lean_fragment`, independent of the author.
Date: 2026-10-24 UTC. Worktree:
`/workspace/shared/witnessed_C1_20261024/witnessed_decompositions`.
No author Lean source, target, or contract was edited by this reviewer.
Reviewer-created probes and logs are under `review/lean_independent/`.

## Hash bound inputs

| Input | SHA-256 |
| --- | --- |
| Unchanged `research/CompletionContract.md` v0.1 | `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e` |
| Frozen `C1_Targets.md` | `7a5d4bb8dd3aa0715c82b73b8c169def2935b98f41addfd0eaaf03a606be244e` |
| `proof/C1_Model_Theorem.md` | `8a05992fe26c456ed1a5c61c5512e7939ed625da76263b58f61940e1a3a0cd7c` |
| `lean/GraphCutFragment.lean` | `344502c147e8d387d6da577725bffbb8d1d2ad452537430d09e66ee93c97442e` |
| `lean/GraphCutAxioms.lean` | `4caf7287b7abb515fcf99872417dc8e62717f8c342d11fccf1e6668e06545d07` |
| Revised `lean/Adapter_Comparison.md` | `42d7507d71314f785b65d56af3c8c674be7ac06e40e5c84c58925156f2777a0a` |
| `lean/TheoremIndex.json` | `e036c1ffeaae0711eb84e104b6e01e4618362f65b75b1f08c3f37355087047a5` |
| Reused `research/workstream_A/rewrite/GraphCoordinates.lean` | `05d0dea6e540641e4302517f50b242e59e37fd5e086a1a8ecca48db16ef97077` |

The contract's C1, §3.4, §13 and Gate 1 clauses, frozen target, pre-attempt
depth review, full P model theorem, adapter, actual A APIs, source, and theorem
index were inspected. `C1_Lean_Math_Depth_Audit_Inputs.json` records the full
reviewed project-source closure, evidence hashes and exact toolchain inputs.

## Fresh independent verification

`lean_independent/rebuild.py` compiled into a reviewer-owned fresh directory,
with that directory first on `LEAN_PATH`. It rebuilt 12 A source modules,
`GraphCoordinates`, and `GraphCutFragment`; it then ran the author's axiom
commands against those freshly rebuilt imports. The A modules include the
complete project-source import closure of the fragment: Core, Examples,
Collections, PathOccurrences, TreeOccurrences, Calculus, FreeCalculus,
FreeExtension, Congruence, QuotientCalculus and PresentedCalculus; Positive
was additionally rebuilt. Existing C1 `.olean` files did not supply evidence.
Lean was 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The pinned mathlib cache was used, not rebuilt from all mathlib sources.

Results are in `lean_independent/rebuild_result.json` and individual logs.
All 28 author axiom reports succeeded with union exactly
`{propext, Classical.choice, Quot.sound}`. There was no `sorryAx`, custom
axiom, or unchecked native-decision oracle. A comment/string-aware screen of
15 project/audit Lean sources found none of `sorry`, `admit`, `sorryAx`,
`native_decide`, `axiom`, `unsafe`, or `implemented_by`. The source hashes
were checked again after compilation. All 28 theorem-index locations and
its four file hashes were independently checked.

`IndependentChecks.lean` adds seven kernel-checked certificates, with seven
standard-only axiom reports, for:

- The two middle graph values are exactly the size-two adjacency matrix
  `[false,true,true,false]`, not merely equal abstract colours.
- Actual A frontier components have endpoint/size sequence
  `(0,1,1),(1,1,2),(1,1,2),(1,2,1)`; after refinement the six sizes are one
  and the corresponding endpoint sequence is retained.
- The retained whole has six vertices and 36 adjacency bits. Both symmetric
  entries for edge `(0,5)` are false in the base whole and true in the altered
  whole. Thus graph storage is not an irrelevant tag or leaf-only statistic.
- An empty graph of grade `0→1` has the SAME graph colour as `emptyColour`,
  still has a unary identity tree, and each designated nullary generator has
  equal actual endpoints, empty graph, and a zero-length path.

Six separately compiled negative fixtures were rejected for the intended
reason, not missing imports: empty graph with unequal endpoints supplied a
nullary; nonempty loop graph supplied a nullary; same endpoints but the wrong
actual graph supplied a replacement; wrong interface supplied at a child;
a reverse `2→0` chain arrow; and an overlapping bipartition. The first four
produced type mismatch diagnostics; the final two produced `decide` proofs
that their validity propositions are false. The empty/unequal-endpoint case
isolates typing from graph size, unlike the author's broader `c0` guard.

The exact runner and results are `run_independent_checks.py` and
`independent_checks_result.json`. An initial inline diagnostic matcher used
the wrong wording for `decide` rejection and flagged two correctly rejected
probes as failures. Its result is preserved in
`independent_checks_result_initial.json`; the corrected runner reran all
checks without changing any Lean fixture or theorem. This was a reviewer
harness issue, not a failed model claim.

Reproduction from the project root:

```bash
source /workspace/shared/witnessed_B_20261024/toolchain_recovery/env.sh
python research/workstream_C1/review/lean_independent/rebuild.py
python research/workstream_C1/review/lean_independent/run_independent_checks.py
```

## Retained data and type erasure audit

`GraphColour` stores vertex count and the entire row-major Boolean adjacency
matrix. Its existential ambient realization is in `Prop`; proof irrelevance
prevents that realization from creating extra location-colours. Conversely,
the adapter represents every ordered simple graph of size at most six by
extending it with isolated ambient vertices. Its faithful matrix decoding and
`enumerate_eq_sort` connect these values to actual canonically labelled graphs.
This comparison, including the converse, is P and is not mislabelled L.

`GraphArrow a b` pairs this graph with a proof of `a.value ≤ b.value`, the
actual unique arrow of the three-object chain. The quiver type and dependent
A path preserve intermediate interfaces. Binary generator outputs use
`le_trans`; nullaries use `le_rfl`. There is no nonthin-arrow erasure claim:
proof-irrelevant grade data are appropriate only because this chosen category
is thin. The arbitrary-category P theorem separately retains actual arrows.
The independent wrong-interface and reverse-arrow rejections show that the
mixed path is not solely an integer-list simulation.

A `BinaryCut` stores actual whole and input graph codes, ordered local block
lists and three interfaces. Its `valid` proof enforces a genuine bipartition
of one represented graph. Input graph fields are checked redundant data,
not unconstrained tags. Canonical block locations remain witness data, not
component colours. Consequently `c1=c2` can hold while its two occurrence
replacements store opposite local partitions. `differentForest` is the
public dependent A `Tree.Substitution`, and `refined` uses the public graft.
The colour-keyed mutation gives a different actual final block sequence.

`graphEvaluate` explicitly retains the whole graph, ordered ambient blocks,
and the actual A frontier. `FullCut` has endpoint indices but no separate
whole-arrow field: this is lossless on its valid image in the chain because
the endpoints determine the arrow. It would NOT suffice for arbitrary K.
The same-profile/different-whole theorem and independent adjacency-bit check
confirm that cross-block information remains in the total witness.

## The exact P and L boundary

The following distinctions are necessary, not optional qualifications:

1. `restrict_trans` is generic in graph size and supplied increasing
   embeddings and proves literal pullback composition. It does not itself
   prove the canonical-image enumeration identity R1. That identity and its
   consequence R2 are proved by increasing-enumeration uniqueness in P.
2. `FullCut` is a raw record, not a Lean subtype asserting partition and grade
   validity, and no graph-semantic `Calc` is constructed in this Lean file.
   The P adapter proves the image of ALL valid `CutTree`s lies in the semantic
   carrier. Its strengthened induction includes disjoint coverage, bounded
   indices, strictly increasing block lists, the exact induced graph at every
   frontier slot, and the composite-arrow property.
3. `liftBlock` has a raw-list `getD 0` fallback. It is not justified by finite
   examples alone. The adapter proves it unreachable: a valid binary cut's
   parent block length equals its input graph size, while the child's
   induction bounds every accessed index by that size. Increasing lookup
   preserves the strengthened block-list order invariant. Thus evaluation
   is precisely canonical lifting, including noncontiguous and reversed
   ordered blocks.
4. The leaf, nullary and binary induction cases identify this evaluator with
   the P graph calculus under the binary/nullary primitive assignment. Code
   faithfulness allows child graph equality even when two ambient realizations
   differ. A2's accepted extension theorem then applies to that genuine P
   target calculus; importing A2 by itself would not have established this.
5. `graph_graft_identity` and `graph_graft_assoc` are postcomposition of actual
   A tree equalities with evaluation. They are correct L statements, but NOT
   formal proofs of arbitrary flat-cut substitution laws. Those unrestricted
   laws, all-size closure and arbitrary finite/nonthin category statements
   are P in `C1_Model_Theorem.md`. This is the frozen §13 boundary, not a
   post-test weakening.

The adapter originally left the increasing-list invariant implicit. I asked
for it explicitly because equal underlying subsets alone would not establish
literal list equality in `FullCut`. The author supplied the range base case
and the preservation by increasing parent lookup; the revised hash above
resolves the issue. The old version and author revision record are retained.
No extra hypothesis or Lean source change was needed.

## A3 connection and depth checks

`Declared.rotation` declares a specific parallel three-leaf local rotation;
it is not defined as the kernel of `graphEvaluate` or by all observed model
equalities. `declared_full_cut_sound` checks full graph witness equality.
`competing_groupings_derivable` uses the actual A3 `Derives.substitute` rule
to substitute the binary third subtree and obtain the two four-leaf trees.
`competing_groupings_equal_in_A3_quotient` then uses the actual
`Presentation.quotient_eq_iff`. Their raw trees are separately proved distinct.
This is a real nonempty equational instance and quotient calculation, not an
unrelated A import. Soundness/factorization for the broader rotation/unit
schema is P; completeness and C5 are not asserted.

The frozen six-vertex base edges, noncontiguous blocks, interface path,
proper opposite binary refinements, full flat-cut grouping equality,
distinct presentation trees, added `(0,5)` cross-edge, and empty-leaf/nullary
separation all occur in the source. The L model admits arbitrary tree depth
and arity generated by binary/nullary nodes; there is no syntax-size
truncation hidden behind the vertex bound. It does not replace the all-arity
P semantic calculus with only its tree-presentable syntax.

Accordingly the cheapest nonpassing routes in §3.4 are excluded: no terminal
model, empty middle blocks, ambient-location colours, equal-colour occurrence
collapse, whole erasure, frontier-only grouping equality, arbitrary semantic
quotient definition, or claim that compiling a datatype proves the model.
The result remains standard graph-restriction/multicategory infrastructure.
It supplies meaningful foundational evidence, not a new mathematical invention
or the scientific integration promised by the full program.

## Assurance limit and stopping condition

This is agent-managed non-author review, not external human certification;
correlated-model limitations remain. I inspected the full P theorem to check
consistency and the semantic bridge, but the dedicated P/C reviewers retain
responsibility for their full independent theorem and finite-domain verdicts.
No result here upgrades the finite tests to unrestricted laws or claims the
supplementary nonidentity-loop category was formalized in this chain-only L
source. That boundary is P/C by the frozen target.

The requested independent L rebuild, data/type/circularity audit, semantic
comparison review, nullary type probes, depth verdict and hash-bound report
are complete. There is no unresolved blocker in this scope. Gate 1 aggregation
and publication of any broader status remain with the parent reviewers; full
C1 and C5/F2 remain OPEN.
