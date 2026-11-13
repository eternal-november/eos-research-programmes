# C3 independent substantive P/X review

Date: 2026-10-25. Reviewer: `/root/review_separation_target_depth`.
Author/lead: `/root/prove_model_separation_theorems`.

## Verdict and bound inputs

**PASS — unrestricted P arguments and explicit X certificates, at the exact
proof hash below. No correction or central missing argument was found.**

- Contract v0.1: `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
- Frozen target: `88ea710752d99cd83d10c85740f825b1c543d58c0f475615c667020bc1aa2825`.
- `proof/C3_Separation_Theorem.md`:
  `0826c2827f300a197973c47108ff9e03b154c74f2a09c9782ae0658c3f4617bc`.

**Correctness verdict:** PASS for the stated all-size/all-arity graph fibres,
encoding, local observation classification, six-row separation and inherited
B2 linkage. **Scientific-depth verdict:** PASS for the frozen C3 obligation:
the full coordinate fibres, distinct domains and repairs meet the promised
scope. These are standard elementary results integrated into the actual
C1/C2 models, not a new major theory or satisfaction of later scientific bundles.

This is not final C3 acceptance. The separate author/independent finite-domain
gate, mutation suite, clean reproduction and parent acceptance remain separate.
No new Lean proof is certified here. C1/C2's downstream-use gates and all other
workstreams retain their existing statuses. This reviewer authored no theorem
or implementation being reviewed and made no changes to author files.
Agent-managed non-author review has correlated-model limitations; no external
human certification occurred.

## Review method

I read the complete 527-line proof and all frozen target statements, then
reconstructed the inverse maps, count arguments, syntax induction and examples.
The actual C1/C2 model definitions and B2 comparison, rather than only the
author's summary of them, were inspected. The pre-attempt target and its
cheapest-route exclusions remain unchanged.

I separately wrote `C3_P_IndependentSpotcheck.py` without importing the author
checker. It constructs typed binary trees with local graph/partition labels,
checks child output graphs and interface grades, and recursively evaluates
their lifted partitions. It also directly reconstructs the relation examples
and support fibres. Its result is auxiliary finite evidence supporting this
review, not a substitute for unrestricted P or the independent full C gate.

## 1. Anchored fibre: the inverse is genuinely complete

Theorem 2.1 has the correct domain: all literal simple graphs on the SAME
ordered vertex set, with the ordered ambient partition fixed. Its codomain
graphs have exactly the block cardinalities. Every unordered pair is in one
and only one internal-block set or the cross-block set. This disjoint
classification justifies both reconstructing internal edges from the restricted
graphs and choosing every cross bit independently; no unmentioned consistency
condition remains among cross bits in the unrestricted simple-graph family.

I checked both inverse directions at the individual edge level. Lifting an
internal pair uses a bijection onto its block, so introduces neither a loop nor
an ambiguity. A cross pair cannot contaminate any restriction. In the reverse
direction, each internal pair has a unique block and a unique local pair, so
the reconstruction recovers every original edge, not just its edge count.
This supplies surjectivity onto every prescribed tuple as well as the claimed
fibre bijection.

The exponent sum over i<j is correct for undirected simple graphs: disjoint
block membership orients a cross pair by its block labels, avoiding a factor
of two. The injection boundary follows for the entire map, not only a selected
fibre. If any cross pair exists, toggling it works above EVERY prescribed block
tuple. Thus Corollary 2.3 gives a uniform failure of a left inverse and the
arbitrary-size two-block family, rather than extrapolating from one example.

All-empty partitions, one nonempty block, m=0 and k=0 are correctly included.
When k=0, the assumed partition forces m=0, and both the graph domain and empty
product are singletons. No counterexample is claimed at that injective boundary.

## 2. Unanchored fibre: embeddings are counted, not silently known

Theorem 3.1 is a different statement from Theorem 2.1. A fixed typed path p
determines the sum m of the leaf sizes and the whole arrow, but not the ambient
blocks or the whole edges. Retaining the partition as the summand index makes
the stated disjoint-union bijection valid. Its inverse constructs a full C1
witness and matches the EXACT p, including actual arrows and intermediate
interfaces. I checked that no extra whole or label choice is omitted.

The permutation count of ordered partitions has stabilizer size product n_i!:
only internal orders of the individual block lists are discarded. There is no
division for equal-sized or isomorphic block graphs, since the blocks remain
ordered occurrences. Multiplication by the constant cross-edge count then gives
the whole fibre size. Empty factors and the empty product give one nullary
witness over the forced empty identity-graded whole. The proof correctly counts
total witnesses, not the number of distinct whole graphs in their image.

The repair map has an explicit inverse onto well-typed admissible records.
It is not injectivity assumed as a recovery hypothesis. Its two data-removal
controls test distinct losses: deleting a cross bit changes recoverable graph
information, whereas deleting B identifies the opposite singleton cuts even
though their full graph, profile and cross-edge set agree. Keeping an unordered
family of blocks also identifies that latter pair. The limitation to these
specified graph records avoids a hidden claim about globally minimal recovery.

## 3. The six rows have the right maps and witnesses

| Row | Substantive verification |
| --- | --- |
| Frontier versus tree | The balanced and right-associated presentations have the same complete path and root. Their root-left subtrees have different constructors, so raw inequality is structural, not an assumed failure of equality checking. |
| Shape versus primitive labels | The two opposite singleton partitions are actual different S_bin generators with identical output and input components. Their corollas have the same shape and different root labels, and graph evaluation actually distinguishes them. |
| Leaf types versus whole | The anchored arbitrary-size theorem fixes the leaf path while varying precisely all cross edges. The total Leaves fibre additionally counts the forgotten block embeddings. The six-vertex edge-05 pair is correctly embedded in this family. |
| Whole versus witness | The opposite cuts have one whole and one exact typed profile but different ordered partitions. Thus this row is stronger than merely choosing two different profiles over the same output. |
| Evaluation versus presentation | Both graph groupings evaluate to one FULL retained cut, while the relation corollas collapse because their specified target fibre is thin. Neither argument equates raw syntax or asserts an undeclared quotient equation. |
| Observation versus semantic object | Obs is a named map on a fixed C2 component fibre. The sparse 2-by-3 relations have the same supports and different membership bits; Truth is a separate injective positive control. No unspecified observation is quantified over. |

The positive syntax repair also passes scrutiny. In Theorem 4.1 each recorded
primitive is an actual typed generator, including its input/output indices.
Consequently its children have prescribed output components. Induction can
recover each child from its own shape, address-restricted labels and that output.
The external leaf and nullary internal node are explicitly different shape
constructors. Root output is indispensable for a bare identity tree and is
retained. No injectivity of Shape or of primitive-label erasure is assumed.

The rows do not mistakenly treat leaf-to-whole, whole-to-witness and
presentation-to-evaluated-witness losses as one projection or as logical
converses. The matrix accurately limits each assertion to its displayed domain.

## 4. Independent six-vertex and relational reconstruction

I verified the local coordinates of both groupings: in the right root support
(1,2,3,4,5), local blocks (0,2) and (1,3,4) lift to (1,3) and (2,4,5).
The final local cut (0,1)/(2) then gives (2,4)/(5). The balanced grouping gives
the same four ambient blocks by a different raw tree. Node grades are the
actual composites in [2], including the two repeated id_1 middle components.

The independent script repeats that construction/evaluation over **all 8,192**
graphs with fixed internal edges 13 and 24. Every case has the same four typed
leaves and full partition under both evaluations, with its own retained whole.
It also checks that assigning the forward cut to occurrence 1 and the reverse
cut to occurrence 2 gives (0),(1),(3),(4),(2),(5), whereas repeating either cut
at both equal-colour occurrences gives a different result.

Independently enumerated block assignments of sizes 1,2,2,1 number **180**.
Thus the reported unanchored count 180 times 8,192 = **1,474,560** is correct;
neither author nor review presents it as a count of distinct six-vertex graphs.

For C2, direct existential composition of the displayed R and S gives exactly
the two-pair diagonal D, properly contained in the four-pair W. The alpha and
beta assignment therefore lands in one actual nonexact containment cell.
Two different realizing intermediate values for (0,0) do not create two cells.
Conversely D and W are different output indices and hence different total
semantic cells despite their common input path. These facts agree with C2's
actual model, not a witness-erasing substitute invented for this task.

## 5. Observation support theorem and its limits

Theorem 7.1 specifies the whole fibre, not just a collision: relations lie in
the prescribed support rectangle and every prescribed row/column is inhabited.
Both implications of this description follow directly from domain/range
equality. Exactly one empty support is impossible; both empty give the empty
relation. A singleton side forces every pair of the rectangle. With both sides
of size at least two, removing one rectangle corner leaves its row and column
inhabited and gives a second relation. This verifies the sharp singleton and
global injectivity boundaries, including empty carriers.

The independent script checks all **104** matrices in the frozen carrier range,
all **105** candidate support pairs and their **56** nonempty fibres. The sparse
2-by-3 collision is correct. These calculations support, but are not needed in
place of, the all-finite-set proof. Truth's injectivity remains intact; loss is
attributed only to the named support-only reduction. No contextual adequacy,
calculus-morphism property, transport theorem or G/I classification is smuggled
into this local result.

## 6. B2 linkage, empty arity and evidence boundaries

Section 9 correctly instantiates the previously proved strict interpretation
comparison. Its object map is evaluation; its arrow map evaluates each forest
entry at the original leaf occurrence. In the six-vertex example the u and v
entries remain different and are placed at different original positions. Both
identity and substitution preservation are supplied by the accepted A2/C1/C2
construction and B2, not inferred merely from a recursive evaluator.

The important negative statements are correct: object noninjectivity does not
contradict raw-source categorical faithfulness, since each fixed raw hom-set is
subsingleton. Different-target refined cuts alone do not prove nonthinness at
one target. C2 cell thinness does not permit erasing the individual entry
profiles or segmentation of semantic refinement tuples. The proof neither
asserts fullness nor imports the open B3/B4/C5 comparison/classification results.

Arity remains unbounded in the P argument; none of its proofs truncates the
number of empty blocks. Finite enumeration is explicitly limited to m<=4,k<=5.
This includes all partitions with no empty blocks and the frozen empty-slot
test range, not every infinite empty padding. The accepted target permits this
sufficient finite domain alongside all-arity P; neither target nor proof claims
a finite-representative reduction of arbitrary typed arrow strings. In
particular, no empty graph slot and its possibly nonidentity arrow is deleted.

The optional product factorization for [2] is legitimate for these graph-fibre
checks: graph restriction/reconstruction uses graph and partition fields, while
composable grades use the full object string. Each pair of such valid data
gives one valid typed witness; empty partitions/paths obey their specified
typing condition. Execution counts must still be distinguished from represented
Cartesian-product counts by the separate C reviewer. No all-category enumeration
claim or arbitrary-category factor cancellation is inferred.

## Final disposition

The review attempted the main shortcut failures: forgetting ambient placements
in the count; an extra symmetry factor; conflating nullaries with empty leaves;
erasing whole indices; using thin C2 cells as latent witness sets; using a
faithfulness statement to promise object recovery; and extrapolating finite
enumeration to all arities. The actual proof avoids each. No repair was required.

The input manifest binds the theorem, target, dependencies, independent source
and auxiliary result. All 578 listed archival baseline files were rechecked as
unchanged. Parent may use this report as the non-author P/X correctness and
C3-specific depth verdict, while awaiting the remaining independent evidence.
