# C1 finite evidence — independent review

Date: 2026-10-24. Reviewer: `verify_graph_cut_certificates`, separate from the
model/finite-code authors. Contract v0.1 C1, §3.3–§3.5 and the complete frozen
target were inspected. This is same-model agent review, not external human
certification.

## Verdict

**PASS for the frozen C evidence of the authorized local C1 milestone.** No
count inflation, omitted frozen finite case, residual mutation-control defect,
or false whole/leaf identification was found in the final author checkpoint.
The author run was reproduced, and a separately authored implementation
**directly executed all 2,745,411 typed associativity cases**; it does not rely
only on the author's factorization claim.

This verdict neither accepts the P theorem nor kernel-checks the L fragment;
those have separate reviewers. Full C1 remains **OPEN**, including required
C5/F2 use. No C3 fibre theorem, C5 completeness, F2 2-Segal claim, broader
scientific acceptance, novelty, or authorization for later work follows.

## Bound inputs and reproduction

All paths below are relative to the repository root. SHA-256:

| Input | Hash |
| --- | --- |
| `research/CompletionContract.md` | `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e` |
| `research/workstream_C1/C1_Targets.md` | `7a5d4bb8dd3aa0715c82b73b8c169def2935b98f41addfd0eaaf03a606be244e` |
| `research/workstream_C1/finite/check_c1.py` | `8cabef32cdcceb25d9de8f6ecb82c2032f869069d9c5afe84f177e3e8a640104` |
| `research/workstream_C1/finite/results.json` | `f8886a0f9f46c6a9f5468c39bdb7f83f62719faa1f84bae713c29630a67d9f61` |
| `research/workstream_C1/finite/DOMAIN.md` | `7462b0331718542639b12236e7a7d87726f69ced6cf20fc35df4f61a950219e9` |
| `research/workstream_C1/finite/CHECKPOINT.json` | `9a280c2e39e9d9a9630d1f4f8d3400a14b606e0d65af7bf8df535e2cbcfc62b0` |

Evidence is under `research/workstream_C1/review/finite_independent/`.
`author_final_reproduced.json` and its log reproduce the final author source;
all deterministic fields, including source hash and complete certificate
payloads, equal the submitted result. Timing and timestamps naturally differ.
`author_snapshot.py` is an exact read-only copy of that source checkpoint.
No author source or result was edited by this reviewer.

Reproduction commands:

```sh
python3 -B research/workstream_C1/finite/check_c1.py \
  --output research/workstream_C1/review/finite_independent/author_final_reproduced.json
python3 -B research/workstream_C1/review/finite_independent/independent_check.py --full-product
python3 -B research/workstream_C1/review/finite_independent/count_domain.py
python3 -B research/workstream_C1/review/finite_independent/supplementary_category.py
```

Independent checker hash:
`cac5930bbda8be566743159ced89be672e643b6bf458140a0c9947ef262642d7`.
Its full-product result hash:
`ddbcbe0e934be388e0b17df898d127ddb3784497c50de4be094867792ef9d439`.
The recorded run passed in 122.808 seconds on Python 3.12.14.

## Independent computation and exact domain

The independent checker imports neither author code nor author results. It
represents a graph by its full Boolean adjacency matrix and a partition by a
vertex-to-slot word plus an explicit arity; omitted labels remain empty slots.
Substitution scans the parent word, counts earlier vertices in the same slot,
and offsets the child's slot number. Restriction uses principal submatrices.
The complete cut also stores the whole grade and every typed arrow triple.
All source validation and comparison use executable exceptions, not removable
Python `assert` statements. The combinatorial and supplementary scripts use
ordinary asserts and were run without optimization.

| Domain/check | Author result | Independent result |
| --- | ---: | ---: |
| All simple graphs on 0–3 vertices | 12 | 12 |
| All outer cuts, arities 0–3, all chain paths | 4,395 | 4,395 |
| Left unit and right unit | 4,395 each | 4,395 each |
| All single-occurrence refinements, local arities 0–2 | 57,156 | 57,156 |
| All nested subset restrictions | 238 | 238 |
| Three-stage local-arity-0/1/2 shapes | 183 | 183 |
| Graph/shape/final-label cases | 91,848 | 91,848 |
| Shape/interface-chain combinations | 3,123 | 3,123 |
| Full typed product | 2,745,411 represented by factorization | **2,745,411 directly executed** |

The author physically performs 91,848 complete cut comparisons at constant
interface 1, plus the separate 3,123 shape/interface checks. Its final JSON and
DOMAIN document accurately distinguish these executed comparisons from the
represented typed product. They must not be described as 2,745,411 separate
author full-cut runs. The independent run now supplies exactly that stronger
direct computation, including nonconstant mixed-interface paths.

### Coverage proof and a third count calculation

Every ordered partition is exactly a function from the vertex set to its
ordered slots. For zero slots there is one such function only for zero
vertices. Every principal-chain typed path is a weakly increasing object word.
Consequently the cut count is

`sum(m=0..3) 2^(m(m-1)/2) * sum(n=0..3) n^m * binomial(n+3,2) = 4395`,

with `0^0=1`. For a selected slot of size s with endpoints a≤b, the numbers of
inner cuts of arities 0, 1, 2 are respectively
`[s=0 and a=b]`, `1`, and `2^s*(b-a+1)`. For a given selected slot there are
`binomial(m,s)*(n-1)^(m-s)` outer labelings. Summing gives 57,156 independently
of either executable cut implementation. Nested subset count is
`sum(m=0..3) 2^(m(m-1)/2)*3^m = 238`.

For associativity, each nested cut sends each vertex to exactly one final
leaf. Every internal support is necessarily the union of the descendant final
supports, and its local coordinates are uniquely their increasing ranks.
Thus final labelings and nested valid vertex assignments are in bijection,
including nullary nodes and empty internal blocks. The independent checker
generates shapes recursively as plane trees of height three rather than using
the author's vectors of local arities. Zero-ary nodes are not discarded.

Let `P0(x)=x` and `P(d+1)(x)=1+Pd(x)+Pd(x)^2`. The coefficients of `P3` count
shapes with L final leaves:

`L=0..8: 13, 21, 37, 38, 35, 22, 12, 4, 1`.

There are `binomial(L+3,2)` possible final chain words. Each internal arrow is
uniquely determined by its contiguous interval of final leaves; an empty
interval has identity grade. This is the thin-chain-specific fact that
justifies the author's factorization, not an assumption about arbitrary
categories. The exact total is

`sum(L=0..8) [x^L]P3 * binomial(L+3,2) * sum(m=0..3) 2^(m(m-1)/2)*L^m`
`= 2745411`.

The separate `count_domain.py` computes these polynomial/integer counts without
importing either checker, and its results agree. The full-product independent
run constructs the typed cut stages and executes both substitution orders for
every case, comparing whole matrix, whole grade, arity, final labels and the
entire arrow sequence. There is no remaining reliance on multiplying unrelated
test counts.

## Six-vertex, nullary and mutation audit

The independent implementation checks the exact frozen graph and block tuple,
not a conveniently reordered substitute. Both middle components are literally
the two-vertex one-edge graph with grade `(1,1,0)`. The forward and reverse
binary inner cuts are distinct retained witnesses, with equal leaf components.
Their independent dispatch yields exactly
`({0},{1},{3},{4},{2},{5})` through the noncontiguous parent blocks.

Both recursively constructed binary trees store actual graph cut nodes and
typed boundaries. They are structurally distinct and evaluate to the same
complete four-block cut. Adding only `(0,5)` preserves all four leaf components
but changes the retained whole matrix and the total cut. Equality of leaves
is never used as equality of witnesses.

Independent negative tests reject overlapping and missing-vertex partitions,
noncomposable arrow strings, wrong composite grades, nonempty nullaries,
unequal-endpoint nullaries, nonidentity-loop nullaries, and graph/grade-mismatched
replacement operations. The one-empty-slot identity differs from the true
zero-slot nullary, and the expected identity/nullary substitutions pass.
All 12 possible empty-graph grades in `[2]×C2` obey exactly the nullary criterion
`a=b and bit=0`. An additional finite category check verifies all 12 two-sided
identities, 40 composable-pair closures and 120 composable triples; the
nonidentity loop squares to identity. This is supplementary boundary evidence,
not exhaustive graph testing over all finite categories.

All six required explicit mutants are killed independently: erasing the whole;
dispatch by equal component rather than occurrence; failing to lift local
coordinates; accepting nullaries from endpoints alone; ignoring internal arrow
composability; and deleting empty slots. In particular, the final author arrow
mutants really execute weakened acceptance predicates on invalid data; they
are not merely labels attached to an unrelated positive check.

## Relation to the actual calculus, not abstract labels

Author `check_c1.py` lines 21–81 define graph, actual typed arrows, whole
components, complete cuts, identity and substitution independently of trees.
The constructor checks exact partition coverage, order within blocks, arity,
composability and whole composite. `leaves()` computes canonical induced graphs;
`substitute()` demands exact replacement whole components, retains the outer
whole, lifts local blocks and concatenates actual arrows. Dataclass equality
therefore compares whole and full witness data, not just a frontier or a label.

The structural correspondence to `WitnessedDecompositions/Calculus.lean` is:

- `Collection.Op c`: cuts with whole c; `profile`: the induced graph/arrow path.
- `CalcData.identity/profile_identity`: the single whole block and arrow.
- `CalcData.subst/profile_subst`: the checked occurrence family and ordered
  concatenation of its exact profiles.
- `Calc.subst_identity/identity_subst/subst_assoc`: precisely the full-witness
  equality checks; canonical profile transports are represented by the same
  ordered Python tuples.
- `Calc.Operation c p`: the subfibre fixing that complete profile, not merely
  endpoints or length.

The P document §§1–7 supplies the uniform proof and names this same mapping.
`FreeExtension.lean:228` really accepts an arbitrary `Calc` and primitive
assignment, and `PresentedCalculus.lean:42` really factors a model of declared
parallel equations. The Python tree evaluator implements identity on leaves
and actual cut substitution at nodes; it does not define graph semantics as
the free tree carrier or a quotient by all observed equalities. The standalone
finite code nevertheless does not instantiate the Lean `Calc` structure or
prove its unrestricted laws. Actual typed A-tree integration and the exact L/P
boundary must remain with the P/L reviewers. Nothing here substitutes a
Python label table for that requirement.

## Initial observations, resolved issues, and limits

The first inspected source was `efc26092…`. Its result pointed to a not-yet-
present DOMAIN file, and its two arrow mutation records were weaker than
executing faulty validators. These observations were promptly sent to the
author. The final checkpoint supplies the explicit coverage proof and actual
mutant predicates; the old source/results are preserved under `finite/history`.
This was an evidence repair, not a reduction of the frozen domain or hypotheses.

Only reviewer-owned files were added. Contract and target hashes are unchanged.
The independent checker was separately authored after reading the specification
and auditing the implementation; it shares mathematical assumptions and a
model family with the author. It is not a formally verified Python program,
an external-human review, or an unrestricted theorem. All six-vertex checks are
the specified certificate, not enumeration of all six-vertex graphs. Counts
are coverage evidence, not scientific contribution measures.

**Remaining C blockers: none at the bound final source.** Promotion of the
overall local milestone still requires the separate P/L reviews and parent
Gate 1 decision; full C1 and downstream scientific obligations remain OPEN.
