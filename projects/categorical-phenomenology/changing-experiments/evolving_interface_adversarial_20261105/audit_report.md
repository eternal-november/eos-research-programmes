# Changing experimental interfaces: adversarial audit

Date: 5 November 2026. Scope: an internal mathematical review for the proposed target, “study how a change in what can be observed or done changes the characterizations available, and how that change interacts with composing systems.”

## Main assessment

A theorem claiming that interface change commutes with characterization and composition is false without separate hypotheses for: comparison variance; closure under actual continuations; joint realizability; exterior separation; native witnesses; and resources. These are independent obligations. Most basic transport claims and counterexamples already occur in the four assigned prior manuscripts. A credible next result should prove a mixed comparison with primitive-level conditions and a substantive example, not rename an existing quotient or assume that its square commutes.

Two especially useful additions to the existing audit are:

1. An explicit supported three-object example where evidence restriction and forgetting a newly added test give a **strict mixed-adjoint comparison**, rather than an exact Beck–Chevalley square.
2. A general warning that **closure of witness tests under disjunction makes their object Dowker complex contractible**. Logical expressiveness can therefore destroy, rather than preserve, informative incidence topology.

Executable standard-library checks accompany the report. They verify the stated finite examples and bounded enumerations; the proofs below, not the enumerations, establish general claims. No Lean or other proof-assistant verification is asserted.

## 1. Type the change before seeking a common comparison

Let H be a state set and E a labelled family of evaluations. For Boolean tests, write C_e for the true column and c_E for the object closure. Write Q_E for equality of E-profiles.

If E is included in F with the same interpretations on the same H, there is a canonical surjection Q_F → Q_E. There is generally no map Q_E → Q_F respecting the states. The criterion for a state-compatible map Q_E → Q_F is exactly ker(profile_E) ⊆ ker(profile_F).

### Finite incomparable-interface witness

Take H = {00,01,10,11}, E = {first coordinate}, F = {second coordinate}. Each quotient has two classes, but neither has a state-compatible map to the other: 00 and 01 agree on E and disagree on F, while 00 and 10 agree on F and disagree on E. Equal cardinalities or abstract quotient isomorphisms do not supply the missing map. The common refinement Q_(E union F) has four classes and maps onto both.

For Boolean FCA, test forgetting F → E instead gives the adjunction

- left adjoint L_F → L_E: A ↦ c_E(A);
- right adjoint L_E → L_F: inclusion of old closed extents.

But object Dowker topology has a simplicial inclusion K_E → K_F in the **opposite** direction to the behavioral quotient and the join-preserving forgetful map. The Chu arrow with object identity goes from the rich-test context to the poor-test context; its full nerve map need not exist. The covariant incidence inclusion goes in the opposite direction and need not have a generator-preserving concept-lattice lift.

This is already a principal lesson of common_generation_note.tex, lines 314–423 and 820–1073. A new heterogeneous framework cannot suppress these directions by calling every arrow “refinement.” If interfaces also change carriers or output types, supply the actual translations or relations. Merely saying that one has more information is not a typed map.

## 2. A mixed change is generally lax, not exact

Suppose E ⊆ F are test families on H and U ⊆ H is retained evidence. All tests are restricted to U without reinterpretation. There are two routes from a fine closed extent A in L_(H,F) to an old-interface extent on U:

- forget tests, then restrict evidence: c_E(A) ∩ U;
- restrict evidence, then forget tests: c_(U,E)(A ∩ U) = c_E(A ∩ U) ∩ U.

Monotonicity always gives

c_E(A ∩ U) ∩ U ⊆ c_E(A) ∩ U.

Equality is not automatic. This is a mixed square: evidence restriction is a right adjoint, while forgetting tests in this direction is a left adjoint. It does **not** contradict strict functoriality of the two covariant Chu left-adjoint lifts, nor strict functoriality of their right adjoints. A manuscript should name precisely which square is being compared.

### Supported, nonempty strict witness

Let H = {a,b,c}, U = {a,b}, with old columns

- p = {a};
- t = H,

and new column q = {a,c}. Take A = {a,c}, a closed extent for F = {p,t,q}.

The first route gives H ∩ U = {a,b}; the second gives c_(U,E)({a}) = {a}. Every involved extent is nonempty and has a common true test, since t is universal. Thus strictness is neither an empty-set nor unsupported-concept artifact. All corresponding object nerves are full simplices, so homotopy cannot detect this lattice-level discrepancy.

### A sufficient exact positive class

Assume U realizes every F-row: for each h in H there is u in U with exactly the same values on every F-test. Then the mixed square is exact on every F-closed extent A.

Proof. If h belongs to A, its row-equivalent representative u also belongs to A, because A is an intersection of F-columns. Every old test true on A ∩ U is therefore true on A. The reverse implication is automatic. Hence A and A ∩ U have identical old common tests, and c_E(A) = c_E(A ∩ U). Restrict to U.

This is a sufficient hypothesis, not a claimed necessary one. A weaker independently usable condition is that, within every F-closed extent, retained evidence witnesses every old-test failure. An exact criterion only on retained output points may be weaker still. Avoid presenting equality itself as a practical certificate for equality.

Finite exhaustive check: all 512 Boolean 3×3 tables, old tests the first two, every retained subset and every fine closed extent. All 15,816 comparisons obeyed the inclusion, 432 were strict, and all 3,099 comparisons satisfying fine-row realization were equal.

## 3. New readouts can break operational congruence

A profile quotient for the newly named readouts need not support the old operations. Let H = {a,b,c}, one readout p = {c}, and transition u(a)=c, u(b)=b, u(c)=c. The readout quotient identifies a and b, but their u-successors differ on p. Adding the continuation test u^(-1)(p) = {a,c} gives three distinct classes and restores the missing distinction for this one transition.

This is not a new minimization theorem. The prior common-generation note already gives the same phenomenon for sampled continuation tests; adaptive_experiment_formation.tex explicitly identifies manufacture-stable completion as partition refinement. The relevant challenge is to derive the correct new continuation family from a certified interface compiler and to prove its interaction with the actual wiring, rather than merely adding visible outputs to a table.

## 4. Pairwise witnesses do not give a joint network witness

Take three binary ports x,y,z with local compatibility relations

x != y, y != z, z != x.

Every relation is nonempty, and both its coordinate projections are surjective. Every two-relation network has two solutions. The full network has none. For a one-point reduced interface, each component has a nonempty reduced profile and every proper two-component network has a witness, but the three-component reduced profile is phantom.

The fact that all local boundary values extend across each edge is not enough for a cyclic network. Pairwise joint-lifting certificates cannot be reused as if they proved the complete joint-lifting condition. This is a simple finite constraint-satisfaction obstruction, not a new discovery. It reinforces the realizability-image span already established in contextual_reduction_wiring.tex.

### A useful tree positive class

Let T be a finite tree. Each vertex v has a nonempty actual fiber D_v over a specified reduced local state. For each edge {u,v}, let R_uv ⊆ D_u × D_v be the allowed actual compatibility relation. Suppose both coordinate projections of every R_uv are surjective. Then every selected actual value at any one vertex extends to a global joint witness.

Proof. Root the tree at that vertex. Starting at its selected value, choose a compatible child value using the relevant surjective projection, recursively down the tree. Each vertex is reached once, and no additional edge creates a later consistency condition. The finite recursion yields a joint assignment.

This provides a concrete sufficient joint-lifting certificate for each reduced network profile when the retained constraint graph is a tree. It fails for the triangle above. It supplies **existence**, not a canonical, equivariant, native, resource-bounded or continuously varying witness. Those require additional structure. For empty fibers or extra global constraints, the theorem does not apply.

Finite exhaustive check: all 27 assignments of nonempty binary domains to a three-node path, with every relation having both coordinate projections surjective. All 99 admitted networks have witnesses extending every local value.

## 5. A new joint test can invalidate old component reductions

Take two binary components whose initial local test families are constant. Their old local quotients and their product have one state. Add the joint test x XOR y. The actual composite now has two behavioral classes. There is no factor from the old one-state component-product quotient to this two-state composite quotient that respects actual states.

Thus even keeping exact actual composition fixed does not preserve reduction soundness under arbitrary new exterior observations. One needs a theorem that every new composite test is constant on the chosen new component-profile fibers, usually established by a contextual substitution/definability condition. A diagram comparing old and new quotients cannot manufacture this condition.

Do not confuse this soundness obstruction with the cyclic phantom-profile obstruction. Here every actual pair exists; the failure is that an old reduction hides a new observable distinction. In the cycle example, the issue is joint existence before any separating test is considered.

## 6. Row distinguishability is not one-run experimental identification

Let the hidden world be (x,y) in {0,1}², with one consumable specimen. Experiment e_x returns x and consumes the specimen; e_y returns y and consumes it. Each experiment is initially enabled. No experiment is enabled after either has run.

The extensional table with both labelled tests has four distinct rows: every pair of worlds differs on at least one initially executable experiment. Yet no observation-based single-run policy identifies the world. Before the first query there is no information with which to choose it; either query leaves two compatible worlds and no specimen for a continuation. Randomization cannot yield sure identification.

The four-state behavioral quotient is not wrong. What is wrong is interpreting that quotient as a jointly obtainable four-way diagnosis. Pairwise separability, extensional repertoire, jointly executable experiment suite, and adaptive identification policy are different objects.

Manufacturing two instruments from the same exclusive raw part gives an analogous failure: each test can be made individually, but their union need not be an attainable installed interface. Counting resources per component is not a certificate for the composite budget. State must include actual stock, authority, device state and observation history whenever they affect future execution.

adaptive_experiment_formation.tex already proves a stronger related destructive-diagnosis impossibility. Its whole-runtime boundary also prevents relabeling a compiled macro as new global computational expressivity.

## 7. Topology is exceptionally sensitive to the test doctrine

### Existing redundant-test obstruction

The three-object complement-of-identity context has the Boolean closed-extent lattice B_3 and an object Dowker circle. Adding the universal test H leaves the closed extents and row quotient unchanged, but fills the triangle and kills H_1. This is explicitly already in common_generation_note.tex, lines 820–870. The accompanying script rechecks it; it is not a new result.

### Disjunction closure collapses the entire object nerve

Let E be a Boolean test family on H, and let H_live be the objects satisfying at least one test. Suppose represented columns are closed under binary unions. For any nonempty finite subset S of H_live, choose for each h in S a test true at h. Their finite disjunction is a represented test true on all S. Therefore every finite subset of H_live is a Dowker face: the object complex is the full simplex on H_live, contractible whenever nonempty.

The result needs no globally true test and holds for infinite H with its ordinary finite-face simplicial complex. Binary disjunction closure suffices because each face is finite. In the finite case a global true test on H_live is already obtained by finitely many such unions.

In contrast, adjoining all **nonempty** finite intersections of existing test columns changes no object Dowker faces. An intersection is contained in every constituent, so any face witnessed by it already has an old witness; the reverse inclusion follows because singleton intersections recover the old tests. But allowing the **empty** conjunction names H and fills the whole simplex.

This sharp distinction is important for a project about changes of characterization language. A semantic Boolean connective need not have a native executable implementation with the same resource contract. Conversely, if its interpreted column really is added to the witness interface, the topological effect above is unavoidable. One must choose a restricted witness-test family or use a different topological construction, not silently include all ordinary logical tests and expect the same informative nerve.

Finite checks establish both closure statements for all 512 Boolean 3×3 contexts. Their general proofs are the elementary witness arguments above.

### Fixed-degree one-bit instability

There is also a fixed-H_1 version of the prior one-bit instability. Start with the 3×3 complement-of-identity block and pad it to n×n with an identity block. All rows and columns are live. The nerve is a circle plus n−3 isolated vertices. Flipping a single diagonal bit in the first block fills its triangle and changes H_1 from dimension 1 to 0, at normalized Hamming distance 1/n². Identity actions are compatible on both tables.

As n grows the perturbation tends to zero while the same degree-one Betti number changes. Thus there is no uniform local constancy of H_1 under normalized entrywise Hamming perturbations, even in this live finite class. This is a direct variation of the existing counterexample, not a priority claim. It does not contradict stability theorems for persistence modules with a specified filtration and an appropriate interleaving metric; no such filtration or metric comparison has been supplied here.

## 8. Separate four kinds of change

An adequate evolving-interface state should distinguish:

1. **Evidence update:** restrict a compatible set of models/configurations while retaining their meanings and physical residual state. Old universally quantified implications may become true because counterexamples were excluded.
2. **Language/interface extension:** add named tests or operations with specified interpretations. At fixed H and fixed meanings, adding columns cannot change whether an implication involving only old columns holds on H.
3. **Theory revision:** retract or replace a selected conjecture. This is not the same as monotone restriction of a model class unless the revision policy explicitly represents it that way.
4. **System change:** manufacture, intervene, wire, consume or alter a state. This requires a transition on actual configurations and a new access contract. It is not justified by updating beliefs alone.

Finite evidence example: old p={a,b}, q={a} on H={a,b} violates p⇒q; retained U={a} satisfies it. Adding unrelated test labels without deleting b cannot change that old implication. This is a logical, not physical, gain.

Do not compose an information-gain theorem with a construction theorem proved from fresh initial resources. The diagnostic endpoint and the construction start must be the same residual configuration, or linked by a supplied native transition.

## 9. Prior-result boundary and duplication checklist

The assigned corpus already contains the following:

- common_generation_note.tex: canonical Chu lattice lift and exact no-Chu extension obstruction, lines 314–423; partial operational topology and exact domains, 599–779; tautology and one-bit failures, 820–890; covariant versus Chu variance and functorial Dowker comparison, 892–1073.
- native_operations_across_doctrines.tex: typed reconstruction comparison with opposite-direction model reduct, 244–323; native compiler square and limits on reflection/resources, 324–351; failure of arrow-shaped arity transport, equivariant lift obstruction, finite lifting CSP, and coherent free-history lifting, 1027–1299.
- contextual_reduction_wiring.tex: canonical comparison span and independent joint-lifting/separation conditions, 291–392; fixed-boundary and covering hypotheses, universal changed-boundary no-go, 393–476; separate behavioral/concept/support/topological adequacy conditions, 1893–2088; comparisons retain exact operational domains, 2089 onward.
- adaptive_experiment_formation.tex: four distinct changes and whole-runtime boundary, 107–170; destructive diagnosis and failure of worldwise witnesses to give one policy, 300–355; finite manufacture-stable completion and resource-exact adaptive comparison, 788–950.

The next contribution should not claim as new: ordinary quotient factorization; partition refinement; naturality after conjugation by an isomorphism; the observation that surjections need not preserve pullbacks over a changed boundary; Dowker duality; a span whose two legs are named as obstructions by definition; or a finite constraint enumeration equivalent to existence by unpacking all axioms.

A stronger useful deliverable would establish an independently checkable class of experimental interface changes and network wirings for which the required mixed comparisons, joint realization and native resource-respecting compilers can all be proved, then show a genuine multi-stage example whose result is not covered by one of the prior fixed-interface theorems. If the general theorem remains out of reach, a precise obstruction theorem plus the supported finite example and tree positive class is preferable to an unqualified new unification claim.

## 10. Verification and files

Run `python finite_checks.py` from this directory, or invoke the script by path. It regenerates `finite_check_results.json`; `check_run.txt` records the current successful run.

Checks include incomparable interfaces, the mixed square, all bounded lax/row-dense cases, topology under tautology, cyclic joint failure, the tree positive class, new-joint-test unsoundness, one-token identification, evidence-versus-language separation, continuation closure, logical closure effects on topology, and fixed-degree instability for sizes 3 through 8.

The enumerations do not prove statements outside their stated finite range. General positive claims are proved in Sections 2, 4 and 7. The report audits proposed stronger claims; it does not assert that the supplied prior manuscripts made those errors.
