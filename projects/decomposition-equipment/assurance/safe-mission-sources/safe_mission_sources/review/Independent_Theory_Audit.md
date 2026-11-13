# Independent theory audit

29 October 2026. Scope: `theory/Safe_Discovery_Mission_Theorem.md` and its finite checker, against `RESEARCH_GATE.md` and the prior-art/target-gate assessments. This is a mathematical and finite-test review, not a hardware or novelty clearance. The experimental mission implementation is not independently certified by this review.

## Finding

The central relational argument is sound within its stated deterministic finite catalogue and exact-observation premises. The acquired relation is genuinely nonproduct; forest inference computes globally extendible candidates without replacing joint compatibility by marginal products. The theorem is conditional on physical segment witnesses and a finite controller certificate; it does not itself establish that safely attainable identifying data or a completing policy exists. The acquired diagnostic forest is supplied/selected instrumentation structure, not a discovered physical interaction graph. Actual response scopes remain unknown and are learned conservatively.

No counterexample to the forest recurrence or the unresolved-candidate observer was found. Several precision/cost issues were communicated to the author and corrected. The corrected code passed the independent tests again. A final isolated-vertex accounting correction was requested; see disposition below.

## Required corrections identified

1. **Relational cost omission.** The final paragraph of §3 gives `O(mM+n)` storage and unary record/support query costs without restricting them to coordinate observations. For the main relational extension, retained diagnostic records/factors, messages/signatures and propagation are additional costs; joint queries need compatibility inference and potentially increased width. This is a presentation error affecting a central research-gate accounting obligation, not a refutation of Theorem 1R.
2. **State must contain the relation.** §5's configuration `k=(s,c,H_1,...,H_m)` omits acquired edge constraints. Two transcripts may have identical marginals but different safe joint decisions. Include the retained factors/relation or explicitly define `k` to contain it.
3. **Checker does not implement the stated fast intersection scheme.** The reference checker individually intersects all incoming messages except one for each orientation. At a high-degree node this costs `O(degree² * |H_i|)`, not the theorem's prefix/suffix conjunction bound. The theorem describes a valid faster algorithm, but the reference implementation must be labeled accordingly, or changed and tested. Signature lookup counts alone do not measure its full runtime work.

## Additional precision recommendations

- Equation (7) should restrict to nonempty knowledge and safe actions with nonempty realizable successor sets. Otherwise universal quantification over an empty successor set admits vacuous winners. Theorem 5 already explicitly excludes this error.
- Lemma 4's exact realization statement is unambiguous for deterministic response transcripts. If physical outcomes are merely an overapproximate support abstraction, independence from the mechanism is not enough to show every abstract sequence is physically realizable. Preserve latent physical state in the relational image, demand an exact Markov abstraction, or qualify the assertion to the recorded response transcript. Sound universal safety can still hold with overapproximation; physical completeness then does not follow.
- The reference to “preceding statistical concentration formulae” in §4 has no referent in this document. The correct statement is simply that the deterministic coverage argument gives no independent-sample concentration guarantee.

## Independent tests

Run `python review/independent_theory_tests.py` from any directory. Results are written to `review/independent_theory_tests.json`.

- 43,200 exact recursive-update cases for observers formed from unions of multiple unresolved candidates, plus response sufficiency and shrinking-domain truncation. This supplements the author's singleton-observer tests.
- All 586 acyclic edge-labeled sum-constraint configurations on four binary constant-response variables, checked against exhaustive fixed-world enumeration.
- Disconnected inconsistent components invalidate every global projection, including otherwise unconstrained components.
- A three-variable sum-one chain retains both candidates at every variable but excludes unequal endpoint choices: globally extendible candidates cannot be assembled independently.
- Two internal-boundary relations with identical boundary projections have different conditional internal states: marginal-only elimination cannot support later reactivation/rejoining.

All tests passed. They are finite implementation evidence, not substitutes for the proof or mission execution validation.

## Detailed obligation review

### Exact persistent nonproduct uncertainty

Fixing the controller's independent random seed makes action choice a function of prior delivered observations. Consequently action adaptivity itself supplies no additional mechanism constraint. Each exact coordinate observation adds a unary constraint; each pair-sum observation adds its actual two-variable constraint. Conjoining these on the original function identifiers retains the same fixed environment. The assumption that ignored public transitions do not reveal additional mechanism information is necessary; extra ignored side channels make this relation conservative rather than exact for richer knowledge.

### Forest algorithm

For a fixed candidate at a separator node, all incident subtrees are disjoint and can be joined independently. Repeated observations on one edge are a single complete response signature, preventing per-row witness switching. Complementing the other endpoint's entire signature therefore implements the exact edge compatibility test. Both directions of every edge are necessary for global projection. Disconnected consistency is checked before claiming global support. Cycles are explicitly rejected rather than silently approximated by loopy propagation. The proof does not license arbitrary joint predicates without including their additional query factor/width.

### Discovery and memory

Canonical essential-function domains avoid reporting syntactic dummy ports as discovered dependencies. If alternatives remain, reporting their union is conservative; reporting the simulator's actual scope would not be justified. The maximum threshold across supported candidates preserves all threshold evaluations and commutes with counter increment/reset. Since accumulated exact evidence only shrinks the relation, subsequent projections only shrink; truncation initializes a smaller observer without recovering discarded history. This does not permit discarding physical-resource monitoring counters or forgetting identities needed by joint queries. The result discovers memory within the supplied run-counter grammar, not arbitrary hidden memory.

### Safe acquisition

No independent sampling or concentration step is needed. Actual counters come from real initial-state guarantees or charged safe synchronization; union-scope coverage uses actual recorded matching contexts. The theorem does not prove that those contexts are safely reachable. The physical segment contract must cover intermediate pulse states, travel to diagnostics, all timing and stopping tails; post-diagnostic information cannot justify an already-unsafe action. Failure of the supplied physical interpretation or structural catalogue remains outside the deterministic learning guarantee.

### Module frame and rejoining

The text correctly requires unchanged identities, counter-provider history, shared resources and full relation or sufficient separator information. Eliminating an internal variable gives valid answers only for retained-boundary queries. Later reactivation needs retained factors/conditional identities; a boundary marginal alone is insufficient. Actual postconditions must imply subsequent preconditions, rather than merely sharing a satisfiable projection. Acyclic composition of finite module certificates yields a finite global ranking after collapsing administrative zero-step transitions. Cyclic invocation needs an independent progress argument.

### Finite mission completion

True-mechanism containment, a universally sound physical action contract, complete represented successor coverage and strict integer rank descent imply a useful safe terminal within the root rank. Abort leaves, deadline failures and safe refusal cannot be counted as goals. Bounds on physical duration and computation must already be discharged by each contract; finite action rank alone does not imply a real-time deadline. The completeness claim is only for the declared finite abstraction and action/observation library, not the physical world. Safe indistinguishability correctly concerns lack of a common completing strategy, not merely inability to identify a model.

## Release boundary

The proof layer is a defensible conditional construction after the accounting/state clarifications. It does not on its own discharge the research gate: the substantive family must show safe acquisition and mission-relevant unresolved coupling, hold out mission combinations, compare an information-equivalent exact reference and honest conservative/fixed-decomposition baselines, and charge discovery, evidence, communication, synthesis and checking separately. The prior-art audit's caution remains valid: acyclic joins, version spaces and ranking certificates are established mechanisms, not a literature-wide novelty result.

## Correction disposition (21:04 UTC)

The author revised §3 to distinguish coordinate costs from retained relational costs, §5 to include `K_D`, (7) to require nonempty knowledge and successors, and Lemma 4 to distinguish response consistency from exact physical trajectory realization. The stray concentration reference now explicitly refers to the predecessor project. I inspected these revisions. The code now uses inward/outward passes with a failure count per candidate to exclude one neighbor in constant time per candidate; the quadratic-degree issue is fixed. All independent tests passed again against that implementation.

One small remaining bound correction was requested: replace `sum_i degree(i)|H_i|` by `sum_i (1+degree(i))|H_i|` in time and storage to account for explicitly returning projections for isolated vertices. An empty forest otherwise makes the displayed expression zero despite nonempty input/output.

Final bound correction verified: equation (12) and cached storage now include `(1+degree(i))|H_i|`. All identified corrections are resolved in the reviewed version. No open proof defect remains from this review. This disposition supersedes the “remaining” wording immediately above, while preserving the audit trail.
