# F2 original-source obligation map (2026-10-31)

Scope: approved F2 verification/acceptance closure only; no I4 work. This is an evidence-location audit, not an acceptance verdict or new theorem. Source files were inspected directly. Existing C results below are reported from their artifacts; this audit did not rerun them.

## Frozen obligation

`/workspace/shared/contract_revision_20261028/final_artifacts/Original_Completion_Contract_v0.1_VERBATIM.md`, **F2 Positive typed finite bridge**: M, positive branch. C1 ordered graph size bound N≥6 and finite three-object category; all-degree simplicial/unital 2-Segal P proof, explicit operation/presentation comparison, every graph through four vertices and degrees through four C verification, exact six-vertex mixed/repeated witness. Required controls: both quadrilateral triangulations, pentagon compatibility, noninjective ordinary Segal, outer induced restrictions discarding cross-block edges, empty-block degeneracies, nonidentity arrows and repeated occurrences. Finite truncation or graph×category product alone does not discharge F1–F3 scientific floor. F1 is a dependency, not a reason to silently expand F2 into I4.

## Canonical path abbreviations

- `BASE=/workspace/shared/contract_revision_20261028`
- `C1=$BASE/extracted/witnessed_decompositions/research/workstream_C1`
- `INT=$BASE/extracted/witnessed_decompositions/research/workstream_integration`
- `GLOBAL=$BASE/structural_extracted/proof/Global_Cut_Repair.md`
- `F4=/workspace/shared/f4_edge_forgetting_20261031`
- `CLUSTER=/workspace/shared/f1_f3_recognition_20261031`

## Exact reusable proof/evidence versus remaining verification

| Obligation | Existing actual evidence | Reuse and missing item |
|---|---|---|
| Every level, arbitrary monotone action, all simplicial identities | GLOBAL §§1–2 defines interval records and induced restriction action for every monotone map; §4 identifies original discrete graph-cut×category-nerve slice | Reuse all-degree argument, explicitly specialize to original literal graph equality and K=[2]. Do not use the larger unrestricted span groupoid as the finite simplicial set. |
| Every triangulation, all degrees | GLOBAL §3 reconstructs unique graph partition recursively from root triangle (0,k,n), retaining whole cross-edges; coefficient equivalence proof; §4 original discrete recovery | Reuse graph recursive gluing plus category-nerve uniqueness, spell out restriction to original slice. Full-faithfulness of inclusion alone is not a proof that an arbitrary subobject inherits 2-Segality: original slice's triangle matching/gluing must be stated. |
| Unital comparison | GLOBAL §3 eq. (3.3), §4 actual identity arrows and empty blocks | Reuse, and check literal set-level unit square: empty principal block + identity arrow is precisely image of inserted empty slot. |
| Degreewise finite, arbitrarily high degenerate degrees | GLOBAL §4; C1 proof §6 bounds graphs but not arity/path length | Reuse; for [2] degree n arrow strings are weakly increasing object sequences length n+1, count binomial(n+3,2). |
| Original C1 operations and substitution | C1 proof/C1_Model_Theorem.md §1 full FlatCut.Operation c p; §§2–5 canonical increasing lift and full occurrence-indexed substitution; GLOBAL §§4–5 original discrete recovery and exact operations | Reuse via principal-edge/long-edge fibre: full graph, partition and full arrow string exactly C1. Grafting corresponds to lifting child partitions through parent increasing inclusions; not reconstructing whole from pieces. |
| Explicit presentation comparison | C1 proof §7 binary/nullary signature S_bin, Tree.extend strict evaluation, Presentation.extend factors declared rotation and unit equations | Already explicit and reusable. It is soundness/universal factorization, not C5 completeness. Do not claim equality of raw trees or quotient completeness. |
| Exhaustive all simple ordered graphs ≤4, all degrees ≤4 | F4 verify_f4.py, verification_readme.md, results.json: 23,531 graph/partition records (levels 1,76,1099,5422,16933), 4,989,903 monotone actions; independent set-based reference; composition factored on lineage atoms over 73,085 map pairs | Graph geometry component is reusable, including all empty/noncontiguous partitions. Existing F4 does not itself certify full F2: add triangulation fibre comparisons and exact category factor. |
| Exact finite three-object category [2] | C1 finite/DOMAIN.md: weakly increasing chains in {0,1,2}, but small cut suite only degree≤3; C1 depth-three shape test is different domain | Need dedicated [2] path checks through degree four (3,6,10,15,21 paths), with factorization proof covering graph×path product. F4 general path suite instead uses C2×[1], two objects, so not interchangeable. |
| Both quadrilateral triangulations / pentagon | GLOBAL §3 all-triangulation gluing theorem; C1 §7 rotations; exact binary grouping fixture | No existing full original F2 finite triangulation implementation located. Need both degree-3 triangulations, five degree-4 triangulations and coherence (same reconstructed whole/partition/path under five flips). |
| Outer restrictions / empty degeneracies | GLOBAL §2 and F4 all-monotone original graph geometry suite | Reuse general coverage, name explicit F2 controls showing cross-edge deletion and empty-slot insertion with actual [2] arrows. |
| Noninjective ordinary Segal | C1 six_vertex() compares frozen G with G+05, same four induced component graphs and same arrows but distinct whole/witness. F4 repeats this comparison and two fixed six-vertex fibres | Reuse exact certificate, explain principal-edge map (not 2-Segal map) is noninjective. |
| Six-vertex mixed/repeated fixture | C1 finite/check_c1.py:six_vertex, proof §8, finite/DOMAIN.md, results.json; independently reviewed in C1/review/C1_Finite_Independent_Review.md | Reuse exact fixture and substitution/presentation checks, preferably replay function in F2. F4 six-vertex regression checks equality of repeated graphs and [2] monotone compositions, not all original repeated substitutions. |

## Exact frozen C1 §8 fixture

Graph on {0,…,5}, edges `{01,12,13,24,34,45}`; ordered blocks `({0},{1,3},{2,4},{5})`; [2] interface path `(0,1,1,1,2)`, actual arrows `0→1,id1,id1,1→2`. Both middle components are the same two-vertex one-edge graph with grade id1. Refine first middle occurrence by local blocks `({0},{1})` and second by `({1},{0})`. Their component lists agree but their cuts differ. Occurrence-wise substitution yields `({0},{1},{3},{4},{2},{5})` (different assignments must never be deduplicated by component value). Actual binary trees `((0,1),(2,3))` and `(0,(1,(2,3)))` evaluate to the same original full four-cut. Add edge 05 to change whole while preserving all four principal pieces. `check_c1.py` lines 149 onward constructs all of this directly; independent label algorithm checks refinement.

## Sources that must not be overstated

1. **C1 old finite suite**: DOMAIN.md explicitly has graph sizes 0–3, outer arities 0–3, 4,395 cuts, 57,156 single-occurrence refinements and 238 nested restrictions; separate depth-three shape suite has 183 shapes/91,848 graph assignments. Good core evidence, not requested F2 m≤4 simplicial domain.
2. **Original integration finite suite**: inspected `INT/finite/{check_integration.py,model.py,DOMAIN.md,AuthorCertificate.json}`. The apparent pentagon in check_integration.py line 203 is a missing-O free-groupoid loop, not a simplicial graph-cut triangulation check. DOMAIN.md final scope explicitly says it does not prove a simplicial object/settle F1–F3. No reusable F2 triangulation implementation found in this extracted source.
3. **Latest F4**: `F4/verification_readme.md` expressly disclaims full F2/every-triangulation coverage. Category is C2×[1], not [2]; only exact six-vertex fixture uses original [2] chain. Its K(F2,2) cocycle checks are negative F4 controls and specifically not 2-Segal.
4. **F1/F3 cluster verifier**: `CLUSTER/verify_cluster_note.md` uses contiguous-clique graphs/compositions and orbit quotients, not all 76 simple ordered graph types through size four; category C2×[1]. Its six-vertex (3,2,1) cluster is not the original six-vertex C1 fixture. The note explicitly disclaims original F2 C certificate.

## Next authorized action / status

No external-access blocker. Reuse proof infrastructure and original C1 fixture; add only the identified finite gaps ([2] factor, original full-graph triangulation comparisons/pentagon and explicit F2 controls), document factorization, and obtain non-author proof/scope and reproducibility review. Those actions are being handled by the parent F2 task; this map does not independently mark F2 ACCEPTED. I4 remains unstarted.
