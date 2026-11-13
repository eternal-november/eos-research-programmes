# C1 P theorem: independent substantive mathematical review

## Verdict and exact scope

**PASS — the P theorem is mathematically sound and meets the cleared local C1
proof target.** No central proof gap, hidden thin-category assumption, or
scope-weakening remains in the reviewed version. This verdict is for P only.
Lean certificates, finite-checker coverage, reproducibility, and the final
LOCAL_VERIFIED / Gate 1 decision require their separate evidence. Full C1 and
its required C5/F2 uses remain **OPEN**.

- Reviewer: `/root/review_graph_cut_target_depth`, non-author of the proof and
  implementation, 2026-10-24. Review is agent-managed, not external human review;
  correlated-model limitations remain.
- Proof: `research/workstream_C1/proof/C1_Model_Theorem.md`, SHA-256
  `8a05992fe26c456ed1a5c61c5512e7939ed625da76263b58f61940e1a3a0cd7c`.
- Cleared target: `research/workstream_C1/C1_Targets.md`, SHA-256
  `7a5d4bb8dd3aa0715c82b73b8c169def2935b98f41addfd0eaaf03a606be244e`.
- Contract v0.1: SHA-256
  `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
- Tree: `/workspace/shared/witnessed_C1_20261024/witnessed_decompositions`.
- Initial proof reviewed: SHA-256
  `2c0ea86e57c5ef5aedfcd2ae03dd2fb044e4222bbd196c5101124d1736f3d07f`,
  preserved byte-for-byte in `research/workstream_C1/history/C1_Model_Theorem_initial.md`.

The reviewer read the full initial and revised proof, reconstructed the
restriction and substitution arguments, checked every mathematical `Calc` field
against actual A source declarations, checked A2/A3/B2 linkage against source,
and manually reconstructed the frozen noncontiguous six-vertex example. Source
citation locations were independently checked against the primary paper. No
proof or implementation file was modified by this reviewer. Corrections were
requested from the lead and then re-inspected; only this review and its input
manifest were written by the reviewer.

## The theorem actually established

For every small set-level category K, every finite ordered simple graph, and all
finite path profiles, the independently defined full flat-cut carrier forms a
path-profile nonsymmetric multicategory. Its operations retain the output
whole/arrow, ordered partition, and actual full input path. Substitution is
occurrence-indexed canonical lifting of inner partitions; identity, profile,
unit, and associativity laws hold as equalities of full witnesses. Restricting
all graph sizes to at most any N is closed under these operations without
truncating arity or tree depth. For finite K, each bounded fixed-arity total
carrier and the binary/nullary primitive signature are finite.

The actual A signature, free-extension interpretation, selected parallel
rotation/unit equations, and their quotient factorization are specified. The
accepted B2 construction applies to the resulting strict interpretation and
retains the tuple of individual refined cuts. These are applications of the
accepted A/B infrastructure, not new freeness, completeness, refinement
faithfulness, or 2-Segal results. The frozen six-vertex mixed-interface example
is proved at P level; its promised L/C verification is not inferred from P.

## Detailed correctness audit

### 1. Carriers, equality, and retained data — PASS

The graph carrier includes both vertex count and all adjacency information. A
component includes the actual K arrow and both endpoints. FlatCut.Op(c) stores
the whole in its dependent index and stores the entire profile and partition in
its value; the total carrier therefore retains the whole. The graph constraints
and composite-arrow equation are proof-only conditions, not extra witness
labels. Nothing depends on recovering cross-block edges from isolated leaves.

This is an independent semantic definition, not a tree carrier renamed or a
quotient chosen to force the desired equalities. Its ordered tuple retains
multiplicity, including empty slots. After the clarification described below,
equality is exactly tuple equality: equal empty entries are not secretly
labelled by additional identities. Nevertheless their indices remain distinct
places for independent substitution. The two-vertex opposite binary cuts later
show genuine parallel distinct operations at the same whole and profile.

### 2. Canonical restrictions — PASS

For U in [m] and V in [|U|], injectivity of epsilon_U gives
|epsilon_U(V)|=|V|. The composite epsilon_U epsilon_V is an increasing bijection
onto exactly epsilon_U(V), so uniqueness of the increasing enumeration proves
R1, including the empty case. Pulling back adjacency along the two equal maps
proves R2, with equal vertex counts; no unlabelled graph isomorphism is used.
Repeating the same argument proves R3 for three stages.

These statements hold for every finite size, noncontiguous U, and arbitrary
order of the outer partition. A reversed order of blocks is not a decreasing
order inside a block: each individual inclusion remains increasing. This
separation is necessary and is used correctly in the opposite-split example.

### 3. Actual category arrows and path expansion — PASS

The snoc induction for comp(p concatenated q) is valid for every ordinary
category; it uses only associativity and identities. Iterating it gives P1 for
any family of paths replacing the actual slots of p. The proof never solves an
arrow factorization or infers an arrow from endpoints, so parallel arrows,
nonidentity loops, and noncancellative categories are allowed.

An empty replacing path has equal endpoints and composite identity. Its output
arrow must therefore be identity, which justifies deleting that factor and
preserves the surrounding path's interfaces. This is a typed constraint, not a
claim that all loops or empty graph components are identity arrows.

An adversarial boundary is an empty graph whose output grade is identity but
whose two empty input grades are both the nonidentity element of C2. Their
composite is identity, so this binary witness is legal; neither input admits a
nullary refinement. The definition and proofs handle this case without treating
empty blocks as deletable units. Thus they do not accidentally rely on the
principal example's thin category.

### 4. Substitution well-definedness and full profile law — PASS

For distinct outer slots, the lifted inner blocks lie in disjoint outer blocks.
For one outer slot, injectivity of its inclusion preserves inner disjointness.
The inner union lifts to the whole outer block, and the outer union covers the
retained whole. If an inner profile is empty, its partition coverage already
forces the outer block to be empty; no nonempty vertices disappear.

R2 proves the graph of each expanded input is precisely the induced graph on
its lifted block. The full inner arrow path supplies all intermediate objects
and arrows; P1 proves its total composite equals the fixed whole arrow. The
advertised profile is literally `Path.expand p q`. The actual A declaration
`Path.slotExpand` goes from expanded slots to dependent pairs, and the proof
uses its inverse in the correct direction when assigning blocks.

This provides every data and well-formedness field needed by `CalcData`, on
arbitrary independently prescribed occurrence families. It is not only a fold
on a preselected tree syntax or a substitution operation at equal-colour keys.

### 5. Both units and actual associativity — PASS

For the right unit, each singleton replacement has the entire canonical local
vertex set as its only block. Lifting recovers the original block, graph, and
arrow; `Path.expand_edges` is the corresponding actual A path equality. This
also covers an outer nullary since its family and tuple are empty.

For the left unit, the only outer block is [m] with identity inclusion. Every
supplied block and arrow is preserved, including the case where the supplied
operation is nullary. The operation identity is available for every output
arrow; it is not restricted to category identity arrows.

For associativity, both constructions retain the same whole. Their blocks at a
three-stage occurrence are respectively
`epsilon_(B_i[C_ij])(D_ijk)` and `epsilon_B_i(epsilon_C_ij(D_ijk))`, equal by R1.
Their complete profiles consist of exactly the same innermost paths, in the
same ordered triples (i,j,k). The revised proof names both `Path.expand_assoc`
and `Path.slotExpand_assoc`, which were inspected in actual source. The latter
identifies the block-function indices under the former's profile equality;
there is no missing switch from equal profile lists to equality of dependent
operation values. Equality of profile and transported tuple, with proof-only
constraints, proves equality in FlatCut.Op(c).

`CalcData.innerFamily` and `composeFamily` use exactly this pullback through
expanded slots. Thus the result fills the actual `Calc.subst_assoc` field,
not a weaker associativity statement with silently chosen matching families.
Empty outer, intermediate, and final fibres have no triple indices, while empty
blocks with nonempty profiles still have their indices. No ordering or
multiplicity is erased. No exchange or contraction principle is introduced.

### 6. Nullaries, closed bounds, and finiteness — PASS

The nullary characterization separately uses the empty partition's coverage,
the type of an empty path, and its identity composite. Necessity and sufficiency
are both proved, and uniqueness is correct in this undecorated carrier. The
one-empty-block identity at (empty,id) differs from the zero-block nullary.
Other empty graph components still have unary identities but no nullaries.

The graph-size bound is genuinely closed: every legal inner graph is an
induced restriction of its output, and substitution keeps the outer whole
unchanged. Empty blocks permit arbitrarily large arities even for N=0; the
proof correctly imposes no arity, depth, or path-length truncation.

The fixed-arity count uses the standard n^m block-label functions, including
the unique empty function when m=n=0 and no function from a nonempty set to
zero blocks. Finite K gives finitely many actual composable arrow strings.
The final proof correctly conditions signature finiteness on finite K; the
construction itself remains valid for small K.

### 7. Exact A1/A2/A3 and B2 linkage — PASS at P level

The quiver has edges (graph, K-arrow), not merely K-arrows. The specified binary
and nullary generators supply A's `Signature.Generator`, source, target, input,
and output fields. Each primitive assignment lands in `M.Operation` at the
exact input path and output. Inspection of `Signature.Assignment` and
`Tree.extend` confirms the claimed strict interpretation is an application of
the real accepted free-extension theorem, after—not instead of—the independent
semantic Calc construction. Its leaves are forced to semantic identities.

Rotation templates retain an ordered triple partition and actual arrows; their
input paths are equal by R2 and their output arrows by category associativity.
Unit templates remove a designated nullary vertex, not an empty-colour leaf.
Their explicit full-cut evaluations agree, so they furnish a real
`Presentation.Model`. Actual `Presentation.extend` factors through the least
parallel substitution congruence; its source type and `projection_extend`
identity were inspected. No completeness or equality-in-one-model shortcut is
used.

For the two four-leaf groupings, take rotation's third block to be B2 union B3
and substitute its identity leaf with the remaining binary subtree. A3's
actual `Derives.substitute` supports exactly this inference; the supplied
third subtree has the required graph/arrow colour. This explains the grouping
comparison inside the declared congruence, not just semantically.

B2's `RefinementComparison.evaluationFunctor` is exactly
`rawFunctor (Tree.extend M assignment)`. Its map uses
`Tree.profileSubstitutionEquiv`, entrywise evaluation, and reindexing by the
interpretation's profile equality. `SemanticRefinement.Arrow` stores the whole
family, with composition by the actual occurrence forest. Inspection confirms
the proof's tuple-preservation statement and identity/composition claims. It
correctly declines to infer categorical quotient identification, semantic
nonthinness, object recovery, or a new fullness/faithfulness theorem.

### 8. Frozen six-vertex calculation — PASS at P level

The four blocks partition [6]. Edges 13 and 24 give the two middle induced
ordered K2 graphs, both carrying id_1. Their colours are literally equal while
their ambient blocks differ. The local partitions ({0},{1}) and ({1},{0})
are parallel distinct binary witnesses; increasing inclusions (1,3) and (2,4)
lift them to ({1},{3}) and ({4},{2}). Together with outer identities this gives
exactly ({0},{1},{3},{4},{2},{5}). Conflating the two equal-colour occurrences
would instead repeat one local order and change the full partition.

For the balanced grouping, the canonical local partitions of {0,1,3} and
{2,4,5} are respectively ({0},{1,2}) and ({0,1},{2}). For the right grouping,
inside {1,2,3,4,5}, blocks {1,3} and {2,4,5} have ranks {0,2} and {1,3,4}.
These explicit ranks in the proof are correct. Lifting yields the same four
flat blocks, full path, and whole in both trees. Their left-root-child shapes
are binary versus leaf, so the raw trees are distinct.

Added edge 05 meets two different singleton blocks; none of the four induced
leaf graphs changes. It is absent from the base whole and present in the second
whole, so the retained total witnesses differ. The proof neither reconstructs
that edge from pieces nor calls this loss a 2-Segal obstruction. The separate
[2] x C2 boundary category really has a nonidentity loop at object 1, making
its nullary exclusion nonvacuous.

## Scientific depth and prior-art audit

The result meets the local C1 uniformity and nondegeneracy floor: arbitrary
finite sizes/categories, explicit strict coordinates, a closed N=6 instance,
actual repeated nonempty colours receiving different proper cuts, competing
trees, and retained-whole nonreconstruction. It is not a single graph test
masquerading as a general theorem.

Its role is foundational semantic infrastructure and validation, not novelty.
The cited baseline is accurate: Gálvez-Carrillo–Kock–Tonks §2.1 presents the graph
restriction/layering example; §§5.1 and 5.5(1) describe restriction species and
induced graph restriction. The article permits broader graph/groupoid settings;
this proof directly treats its ordered simple-graph, arrow-typed set-level
specialization. No all-degree theorem is imported here. [Primary paper,
§§2.1, 5.1, 5.5(1)](https://arxiv.org/pdf/1708.02570)

The cheap legitimate reuse route identified in pre-review has therefore not
been used to evade scope: the semantic carrier and laws are proved directly,
and the A/B applications are explicit. Required later C5/F2 integration remains
an unsatisfied conjunct of full C1 acceptance.

## Defect log and resolution

1. **Unqualified finiteness in §7:** the initial text called S_bin finite while
   opening with arbitrary small K. Corrected to “finite when K is finite.” The
   model theorem was never dependent on signature finiteness; the contractual
   finite-category instance is unchanged. Resolved.
2. **Premature evidence wording in §8:** the initial heading said independently
   checked while L/C work was pending. Corrected to “for independent L/C
   checking.” No L/C verdict is inferred here. Resolved.
3. **Equal empty entries:** the initial sentence suggested changing the order
   of equal empty entries always changes the tuple. Corrected to distinguish
   tuple data from occurrence indices; no extra witness identities are added.
   The already defined carrier and laws are unchanged. Resolved.
4. **Actual occurrence associator citation:** requested precision was supplied
   by citing `Path.slotExpand_assoc` alongside `Path.expand_assoc`. Both were
   checked in actual source. This closes an exposition/API-traceability issue,
   not a change in mathematical hypotheses. Resolved.

The original proof remains preserved with its initial hash; the revision
register records these corrections. No rejected counterexample, material
weakening, or unapproved new theorem branch was used. There are no remaining
P-proof defects requiring action.

## Remaining acceptance conditions

This report recommends recording the P component as independently verified.
It does not mark the complete local C1 milestone or Gate 1 accepted. Attach the
separate substantive Lean-fragment review, finite-domain/independent-checker
review, dependency/axiom/build evidence, and final reproducibility before the
parent records any such decision. Full C1, A4's larger integration, C5/F2, and
other unactivated obligations retain their existing OPEN status. The precise
proof hash above is the reviewed artifact; later mathematical edits require
review of the changed statements and arguments.
