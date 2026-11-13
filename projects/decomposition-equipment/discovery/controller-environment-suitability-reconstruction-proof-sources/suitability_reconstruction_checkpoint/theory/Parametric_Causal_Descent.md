# Context safe causal descent with the physical tables retained

## Why the physical table must remain a parameter

The Horn criterion in Causal_Constraint_Descent preserves code assignments for which SOME update/decoder tables exist. That is not sufficient for unrestricted reuse in a context sharing the same physical table. The two requirements u(0,o)=0 and u(0,o)=1 are each separately functional but cannot hold for one u. Likewise terminal demand {a,b} and demand {a} are each nonempty, but a context requiring {b} distinguishes them. Projecting away the actual table choices before composition loses exactly this information.

This note gives the stronger, table-parametric recognition theorem. It retains the SAME physical function symbols on both sides and in every context. Its standard logical engine is finite ground equality with uninterpreted functions and finite enumerated data. The result is not a new SMT decision procedure. It specifies an exact translation and a context-safe acceptance boundary for the causal decomposition data.

## 1 The retained operational signature

Memory/register sorts are arbitrary nonempty finite sets. Observation, request and response sorts are declared nonempty finite enumerated sets with named, pairwise distinct values. Every physical primitive identifier tau has ONE function symbol (or a tuple of coordinate symbols) with exactly its permitted memory and delivered-observation input ports and its memory/action output ports. Repeated occurrences retain that same symbol. Hidden fields are not added as arguments.

A code point for an actual history/register occurrence is a constant of its memory sort. Actual record rows give ground equations such as

    u_tau(code(h), observed_value) = code(h_next).

A terminal requirement retains the actual decoder application:

    d_delta(code(h), delivered_value) belongs to A(w).

Anchors and reset requirements are equalities of actual code-point terms. If an action output controls which record obligations apply, it remains a finite-valued term, and the guarded obligation is kept as a ground implication, for example

    alpha(code(h),obs)=a  implies  u(code(h),obs,a,reply)=code(h_next).

Membership, guards, conjunctions and finite disjunctions are therefore finite Boolean combinations of ground equalities and disequalities. Nothing selects a fresh table after a hidden world or context is chosen.

The actual fine-to-coarse record/interface maps must compile BOTH descriptions into one common retained hardware signature. Coarse code assignments are pulled back through the specified history maps; delivered-value translations must be explicitly implemented or be specified static interface maps. A source primitive is not silently replaced by an unrelated function symbol. If a physical adapter is needed, its tables and stores are retained in the signature and charged to the architecture.

Write F for the resulting fine obligations and G for the coarse obligations in this common signature. These are FINITE ground presentations extracted from actual records. The criterion below does not replace the finite-architecture all-history proof: a finite trace sample by itself is not an exhaustive operational specification.

## 2 Exact finite countermodel test

To test whether F entails G for all finite memories and all interpretations of the SAME retained tables, test satisfiability of F and not G.

A complete finite procedure is:

1. List all ground subterms appearing in F and G, and include every named value of every finite enumerated sort.
2. Enumerate the finitely many Boolean cases of the formula and the possible named values of the finite-enumeration-sorted terms. In a case, positive equality atoms become equations and negative atoms become disequalities. Add the chosen enumeration equations and distinctness of its different named values.
3. Compute sorted congruence closure on the finite term set. If any required disequality has equal endpoints, reject the case.
4. If a case survives, construct a model. Each memory sort consists of its congruence classes of ground terms, or a singleton if it has no terms. Every mentioned function application receives its recorded output class/value. Congruence ensures this is a function of its argument tuple. Extend the SAME function arbitrarily to unmentioned tuples, using an existing value of the output sort. Enumerated sorts are exactly their declared named values.

The enumeration step may be expensive. No polynomial bound or new solver technology is claimed. For the pure-update-equation plus terminal-decoder fragment, one can avoid general Boolean case analysis: compute memory congruence closure, group decoder applications with congruent inputs, and intersect their allowed action sets. Empty intersections are inconsistency; an additional demanded set is entailed exactly when the forced allowed intersection is contained in it. Guarded action-dependent obligations use the general finite case procedure.

### Theorem 1 Uniform table parametric recognition

The procedure returns no model exactly when every interpretation of the retained signature on nonempty finite memory carriers satisfying F also satisfies G. If it returns a model, that model gives actual finite code values and ONE total table per physical primitive satisfying F and failing G. Each memory carrier has at most max(1,number of ground subterms of its sort) values.

Proof. Any actual satisfying interpretation determines a Boolean case, values for every enumerated term, and equality/disequality relations consistent with congruence. Hence its case survives. Conversely the class construction in step 4 respects all equations, disequalities, ground Boolean conditions and enumeration values of a surviving case. Functionality follows because two applications with congruent arguments have congruent outputs. Total extension changes no mentioned application. All constructed carriers are finite and nonempty. QED.

Run the test in both directions to recognize table-parametric equivalence. If the actual interface map already proves G implies F, only the reverse test is needed.

The exact quantification is over ALL finite carrier sizes. At one smaller fixed budget there may be extra pigeonhole consequences, so a returned countermodel need not fit that smaller budget. It is a bounded, explicit counterimplementation at the reported resource size. Passing the uniform test, however, preserves every supplied finite budget and every installed-table interpretation in the declared signature.

If hardware tables are restricted to a finite library, uniform equivalence remains sufficient because it holds for the restricted interpretations too. It need not be necessary for that library. For exact library-relative recognition, incorporate the actual finite library restrictions into the fixed-budget case problem. The theorem does not prove that its unrestricted countermodel is realizable by an unspecified gate library.

## 3 Context closure and actual typed substitution

### Theorem 2 Retained-table contextuality

If F and G are table-parametrically equivalent, then they remain equivalent after:

- adjoining any finite context formula H over the SAME physical table symbols;
- introducing fresh history/register code points and explicitly identifying ports by equations;
- consistently substituting well-sorted ground terms for code points;
- composing already certified interface translations.

Proof. The first two operations are conjunction with extra constraints in each finite interpretation. Equal truth values of F and G remain equal after conjunction. For term substitution, interpreting the replacement terms supplies a valuation of the original code points; the original universal equivalence applies to that valuation. Composition applies the equivalence twice to the same physical interpretation. QED.

This is the precise reason retained function symbols repair the shared-table problem. New mixed pairs of rows need not be guessed: in the combined ground presentation, two rows with the same evaluated primitive inputs constrain the SAME function application. Congruence supplies the induced equality automatically. Similarly, the SAME decoder application must satisfy the intersection of all its actual context demands. A context cannot choose another decoder merely because each fragment separately has a nonempty demand intersection.

For the original spatial typed calculus, a separate extraction lemma is still required: compatible-tuple substitution must produce exactly these added actual rows, shared table symbols, boundary code identifications and representation-map terms, with occurrence addresses retained. The companion typed presentation proof must establish that lemma on its declared model. Once it does, the logical closure above certifies every finite generated context. It does not turn spatial substitution into temporal concatenation or license unlisted semantic crossings.

The context statement retains stores and code points. Erasing a physical store, changing its owner, forgetting a budget, changing the exposed observations, or existentially hiding a table choice is not merely conjunction or term substitution. Such operations require their own interface comparison. The theorem must not be used to hide an unbounded protocol counter or to permit a fresh implementation choice in each branch.

## 4 Relation to weaker semantic preservation

Three different claims must remain separate:

1. Some fine implementation exists at a budget.
2. Every coarse code assignment valid after fine pullback remains valid coarsely, possibly after reconstructing its tables. The Horn/forbidden-pattern criterion checks this in its equality fragment.
3. The SAME retained code values AND physical tables satisfy the fine and coarse obligations, even in additional sharing contexts. The present ground-function criterion checks this stronger property.

Claim 3 implies claim 2 in the appropriate common-signature setting, and both imply suitable existence statements. The converses fail. Neither says that every fine controller using information erased by the interface map has a coarse representation.

The coupled target-block environment family exhibits a complementary limit: identical partial chart images do not determine the actual whole matching, and that matching changes the required controller memory exponentially. A pointwise table-preservation theorem cannot invent the missing environmental correlation. Its record premises must describe the admitted whole possibilities correctly.

## 5 Attribution and research boundary

Ground equality, congruence closure and finite-model construction are established machinery; the standard QF_UF setting is documented by SMT-LIB: https://smt-lib.org/logics.shtml . Finite enumerated sorts are handled here explicitly by case assignment. The contribution sought in this research program is the extraction of the correct retained-table operational obligations from typed decomposition witnesses, the exact capability-preservation boundary, and its interaction with actual crossing/refinement/interface changes, not a new name for SMT.

This theorem is about finite actual presentations and their generated contexts. It does not decide unrestricted distributed synthesis, certify an empirically learned environment, or infer probabilities from nondeterministic support. Those would require additional theorems rather than an expanded reading of the present one.
