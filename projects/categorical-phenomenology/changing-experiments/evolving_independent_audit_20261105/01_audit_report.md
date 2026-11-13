# Independent adversarial audit: evolving experimental interfaces

Audit date: 5 November 2026. The scope is mathematical correctness, variance, semantic hypotheses, reproducible finite checks, and separation from the preceding common-generation result. This is not a formal proof-assistant certification or an exhaustive priority assessment.

## Verdict

The substantive theorems pass this audit under their explicitly supplied deterministic, response-preserving, and witness-semantics hypotheses. One material defect in the initial outline was found and corrected during the audit: least repair must support **every retained and newly admitted operation**, not only added operations. The newer source-ready operational theorem has the corrected statement and a regression example.

No counterexample was found to the pointwise Kan/finality theorem, its Bool and retained-category variants, or the three resource-matrix criteria. Independent computation confirms the CNOT/reset claims, the one-pass obstruction, 6,980 least-repair cases, 20,940 exactness comparisons, and 73,200 resource lifting categories, including ternary arity cases not covered by the original resource suite.

A remaining proof-wording qualification was sent to the assembler: response-label equivariance does not reconstruct raw state maps when tests are nonseparating. Fix the shared state/program interpretation explicitly, or conclude only equality of the induced quotient/FCA actions and exact domains.

## Sources examined

- `evolving_bridge_research_20261105/01_theorems_and_proof_draft.md`, before and after its correction.
- `evolving_bridge_research_20261105/evolving_incidence_source_ready.tex`, including the expanded supported-topology, wiring, and response-transfer sections.
- `interface_composition_theorem_20261105_1420/01_theorem_draft.md`.
- `interface_composition_theorem_20261105_1420/02_resource_classification.md`.
- `interface_composition_theorem_20261105_1420/source_ready_section.tex`.
- `contextad_change_investigation_20261105/contextad_change_bridge.tex`.
- The saved predecessor `contextad_change_investigation_20261105/source_snapshots/common_generation_note.tex`.
- Original verification scripts and their results, read but not imported into the independent checks.
- Primary contextad source: Capucci–Myers, [arXiv:2410.21889v2](https://arxiv.org/pdf/2410.21889v2). The title, date, page count, Definition 5.25, Examples 5.33 and 5.35, Definition 5.36, and equations (5.6.20)–(5.6.21) were checked directly.

## 1. Material correction: old operations are not redundant on new tests

The first outline called the generated Moore family the least extension supporting “every added operation,” and called the quotient the coarsest “new-operation congruence.” Both formulations were too weak.

Counterexample: the carrier is {0,1,2}; the old operation fixes 0 and swaps 1 and 2; the old test family is empty. Add the seed {1} and add no operations. Merely adjoining the seed yields extents {{1},{0,1,2}} and row classes {{1},{0,2}}. Full native closure must also contain the test {2}, so its extents are {∅,{1},{2},{0,1,2}} and its row classes are the three singletons.

The corrected statement requires inverse-image stability, equivalently marked complete-join actions, for the entire enlarged operation category. The exactness section must generate under the whole resulting signature as well. The current outline and source-ready theorem now do so.

The fixed-context extension test used in the repair proof is valid. If a complete-join map carries each object marking γ(x) to γ(fx), then f[cl(U)] is contained in cl(f[U]). Applying this to U=f⁻¹(B), with B closed, proves f⁻¹(B) is closed. Conversely inverse-image closure gives the adjunction cl(f[-]) ⊣ f⁻¹. Intersections and all native preimages therefore give the least repair.

## 2. Mixed variance and growth

The directions are correct:

- more tests give a finer state quotient and a canonical surjection Q_new → Q_old;
- the old Moore family includes into the new as a complete-meet map;
- its left adjoint is old closure M_new → M_old, preserving all joins and object markings;
- the object nerve includes forward;
- forward lattice inclusions generally preserve marked states and actions only by inequalities, not equalities.

For a shared operation, inverse-image inclusions commute literally. Taking left adjoints proves the strict backward action square. This avoids assuming the desired comparison. New operations need not have any old action.

The expanded supported-core result is sound: old closed, supported extents remain closed and supported after enrichment; new closure is contained in old closure; the pointwise order comparison supplies the claimed homotopy. Action domains can strictly grow even on old simplices. The source correctly says these are maps of action spans rather than an automatic natural transformation of partial maps with unchanged domains.

## 3. Pointwise Kan comparison and representables

The cell χ:V(∏u_i)⇒u_0W has the correct direction to define K_a:(W↓a)→(V↓u_0a). The source evidence diagram is exactly the target diagram pulled back by K_a, so the displayed colimit map exists without exactness assumptions.

The finality criterion is not overclaimed despite testing only external-product diagrams. Product covariant representables are representables on the product category. Their target colimit is B_0(V(b_i),u_0a). On the source, the fiber over f is exactly the connected-component set of the displayed factorization category. The colimit identifications preserve f, so they cannot spuriously connect different fibers. Universal bijectivity therefore detects nonempty connected fibers, hence finality.

The coherence formula is correctly typed. For successive squares, the induced K is the composite K, and the two expressions for the composite cell agree by naturality of the second cell. No operad, feedback structure, or contextad is thereby supplied automatically.

## 4. Bool, Set, and retained-category semantics

The Bool condition correctly asks for a lift of some arrow with given endpoints, not each parallel arrow separately. Truth-valued diagrams cannot distinguish parallel arrows. In a thin category this reduces to nonemptiness of each lifting category.

The Set condition additionally detects disconnected lifts. It does not demand invertible morphisms or categorical equivalence.

The retained-witness construction is expressly the Grothendieck total category, not an unspecified Cat-valued Kan extension. Taking all evidence categories terminal makes its comparison equal to K. Thus universal categorical equivalence forces K to be an equivalence. Conversely an equivalence K gives fully faithful and essentially surjective total-category comparison. Contractible lifting categories alone do not imply this stronger result.

These distinctions are essential semantic choices. They cannot be advertised as a classification of all possible native witness models.

## 5. Resource classification

For finite arity n≥2 and nonnegative integer matrices:

- Bool exactness iff every column is zero or a basis vector.
- Set exactness iff nonzero columns are distinct basis vectors; zero columns are allowed.
- Equivalence of the specified retained witness categories iff all columns are distinct basis vectors, with no zero columns.

The proofs survive adversarial checks. A column with total weight at least two can be split between two demands that a single indivisible source unit cannot serve. Duplicate basis columns give exactly two disconnected exhausted allocations. A partial coordinate injection gives a least lift for every demand, ensuring finality. A zero column leaves a nontrivial allocation poset over the terminal target decomposition at zero budget, obstructing equivalence. A genuine coordinate injection induces a decomposition-poset isomorphism.

The quantifier n≥2 matters: for unary convolution each decomposition category has its budget as terminal object, so the Bool/Set obstruction need not occur. The current classification states the correct arity restriction.

The separate manufacture theorem compares preservation of joins and has a row-support criterion. C=[2] and C=[1 1] correctly separate the new Bool criterion from that old criterion. The new Set criterion is a proper subset of each applicable universal class, rather than a reformulation of either.

## 6. Response cocones and the actual semantic bridge

The hypothesis ε:D⇒constant P(S) is substantive. In standard terminology it is a **cocone**. Naturality requires every transported label to preserve its entire response column. The source must use precisely its pullback. Under those hypotheses, the colimit comparison is indeed a morphism in Set/P(S).

A bijection then is an isomorphism of labelled incidence contexts. A merely surjective comparison gives equality of evaluated column sets, which is enough for row equivalence, extent-based FCA, supported extent cores, and the object-side nerve. It is not enough for a bijection of labelled tests or a categorical equivalence of witnesses. A resource mismatch need not alter any downstream extensional invariant if lost or duplicated labels have duplicate responses.

Two small tests show why the hypotheses cannot be omitted:

1. For a diagram with one arrow and singleton label sets, assigning the transported source label response {s} and the target label response ∅ does not give a natural cocone. The colimit identifies the labels, but response evaluation cannot descend consistently.
2. On a two-state carrier with only a universal test, distinct constant state maps act identically on all test labels. Label-action equivariance therefore does not identify the raw state transformations or the vertex maps on a full object nerve. It can still identify the induced row and FCA actions and their domains. Fixing one shared state/program semantics prevents this ambiguity.

The companion source currently states compatible response cones and an explicit native precomposition requirement. The assembler was asked to replace the proof phrase suggesting reconstruction of raw state maps with the precise quotient/FCA conclusion, and to state the shared interpretation when transporting actual state maps.

## 7. Wiring and finite examples

The full source theorem uses the realizable profile image L⊆Q_X×Q_Y, not an assumed full product. Its local extent family is exactly the family of restricted rectangles P∩(A×B). Component experiment liftability is explicitly a native certificate with π_X ũ=uπ_X or its Y counterpart; it need not hold for a constrained carrier or shared resources.

Given this liftability, the inclusions and fixed-point argument for F_joint=Gen_T(F_local) are valid. The state, rectangle-preimage, and support-covering criteria follow from the repair tests. Componentwise native primitives preserve the local column family. The standalone source avoids the outline's vague “product formula”: a rectangle family is generally not the direct product lattice, because empty-factor rectangles can coincide and P may impose further identifications.

Independent checks confirm:

- local square: 4 columns, 4 rows, 10 extents, Betti numbers (1,1,0,0);
- CNOT closure: 6 columns, 4 rows, 12 extents, K4 with no triangular faces, Betti numbers (1,3,0,0);
- CNOT/reset closure: 8 columns, 4 rows, the same 12 extents, full 3-simplex, Betti numbers (1,0,0,0);
- the mixed transformation monoid has four functions, so no hidden longer-word behavior is omitted;
- CNOT violates the old marked complete-join extension criterion on {00,11};
- the four-state one-pass example gains the missing {2} column only after allowing the mixed word “b then a.”

The reachable automaton example is also correct: old a sends every state to 0; adding b=(0,0,1) introduces {0,1}, separates all three states, and makes each reachable from initial state 2. Its two-to-three extent-chain change does not change the already-full nerve.

## 8. Contextad connection and boundary to the predecessor

The contextad comparison's lineator has the correct type e'G→Fe. The grade unit/multiplication comparisons, not the lineator itself, are required invertible. The induced body is F(f)ℓ, and the composition-grade calculation uses cartesian transport in the right direction. The primary v2 source supports these conventions. Its “cartesian square” wording refers to a map of fibrations, so the manuscript correctly avoids interpreting it as an actual pullback square.

The reader example correctly reverses the environment map and program translation. It explicitly does not invent a canonical state map E→E'. The orbit example correctly provides an oplax, generally noninvertible pullback comparison; its lost relative bit is real.

The common-generation predecessor already proves the Chu lattice adjunction, object marking, exact partial domains, their composition, the support/topology comparison, and the universal-column counterexample. The new drafts accurately credit these. The present increment is the generated changing interface, least simultaneous repair, strict backward versus lax forward coherence, explicit operational wiring criteria, and the separately supplied decomposition exactness classification. There is no justified claim here of reconstructing a native contextad or all physical executions from its behavioral quotient.

## Reproducibility

Run `python check_independent.py` from this directory. It imports no research code and uses finite sets, direct closure tests, dense mod-2 boundary matrices, and unit-step allocation connectivity.

The output is `independent_checks.json`; `check_run.log` preserves the completed run. The finite suites are sanity checks and regression tests, not substitutes for the general proofs.
