# C2 local relation-interface milestone: pre-proof frozen target

Contract: CompletionContract.md v0.1, SHA256
47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e.
Authorization: C2 local model only. Positive branch, class M; no weakening and
no obstruction-as-completion. Full C2 remains OPEN because downstream D2/E
use is mandatory and not authorized here. C3 and later work are not activated.
Baseline: delivered C1 ZIP b13f4d74a04cf60b58a0c63179668714e2101b8e7cc3c83629d11e23a587734e,
all 445 existing files preserved exactly. Additions only.

## Complete C2 acceptance clause (unchanged)

Class and claim: M. Develop a second model with genuinely different semantics
and explicit boundary changes.
Inputs: Finite interface sets; binary relations as components; compositional
containment or equality as separately declared witness conditions.
Artifact: The model definition, substitution laws, exact versus nonexact
witnesses, and interface-restriction maps. Include witnesses whose whole relation
strictly contains the composite relation so that exactness is not built into
the definition.
Discharge: P for the family and L or independently checked C for the finite
certificates used elsewhere. Clarify that a posetal relational semantics may
identify different primitive or presentation witnesses; that loss is a property
to analyze, not a reason to equate the syntax.
Tests: At least three interface sets; unequal cardinalities; a nonempty composite;
a strict containment witness; and a non-surjective intermediate boundary map
that removes intermediate relational witnesses and makes the comparison strict.
Containment cells may survive even when exactness fails.
Dependencies: A1, A2. Full obligation status: OPEN.
Minimum floor: Prove the parameterized relational model and its actual interface
comparison maps, then use it in D2/E. A singleton relation example or a
containment/equality conflation does not pass. Familiar baseline, no novelty
by renaming. Section 3.4 pre-proof non-author review and section 13 formalization
boundary apply; no author build or finite test substitutes for uniform P.

## Frozen model, quantifiers and target theorems

T1. For EVERY index set I and family X_i of finite sets (empty sets allowed),
components J(i,j) are ALL subsets of X_i x X_j, not just nonempty or total
relations. Every finite ordered composable path p=(R_1,...,R_n), n>=0, retains
its entire sequence of interface labels; no arity or tree-depth bound.
C(p)(x_0,x_n) means existence of a tuple x_1,...,x_{n-1} making every edge true
when n>=1; C(empty at i)=Delta(X_i). Witness fibre M_le(p;W) is the singleton
if C(p) subseteq W and empty otherwise. Separate M_eq(p;W) uses C(p)=W.
W is independent supplied data. A relational realization tuple is NOT a
primitive witness label or an operation payload in these posetal fibres.

T2. Define identity on R by profile [R] and containment reflexivity. Given
outer cell (R_1,...,R_n)<=W and for EACH OCCURRENCE i an inner cell q_i<=R_i,
substitution has concatenated typed profile q_1...q_n and same W. Prove
existence via flattening C(concat q_i)=C(C(q_1),...,C(q_n)) and monotonicity;
prove both units and associativity on operations with full profile transports.
Prove M_eq is a subcalculus and inclusion M_eq -> M_le is a strict
structure-preserving morphism. Properness is certified by an inhabited named
example, NOT asserted for every family (empty families/all-empty carriers
can give equality). Do not assert all containment cells are exact. The empty outer profile is only a loop; a
nullary inner cell requires Delta subseteq R_i and is allowed only at a loop.
A singleton identity operation is not a primitive witness or a nullary unit.
No empty finite set is excluded to make a converse vacuously true.

T3. For EVERY pair of finite sets and maps f:A'->A, g:B'->B, define
Res_{f,g}(R)={(a',b') | R(f(a'),g(b'))}. Give membership-level maps, identity
and iterated-restriction laws. For EVERY finite path and boundary maps
f_i:X'_i->X_i, distinguish:
  (a) C(Res_{f_0,f_1}R_1,...,Res_{f_{n-1},f_n}R_n), and
  (b) Res_{f_0,f_n}(C(R_1,...,R_n)).
There is an inclusion (a) subseteq (b), and an explicit map on realizing tuples
by coordinatewise f_i for n>=1; it need not be injective or surjective. For
n=0 the same map f_0 occurs at both ends and comparison is Delta(X'_0)
subseteq Res_{f_0,f_0}Delta(X_0), i.e. inclusion into the kernel pair.
Thus EVERY containment cell pulls back to a containment cell with whole
Res W. Prove the restriction maps preserve occurrencewise substitution under
CONSISTENT maps on all interfaces of the substituted forest; state whether
this is a fibrewise comparison or a base-changing morphism, never silently
an A.Calc.Hom on different component quivers. Exactness is NOT generally
preserved. Give sufficient equality conditions for n>=1 (all INTERNAL f_i
surjective; endpoints arbitrary) and n=0 (f_0 injective), without claiming
D2's sharp map-class classification or arbitrary equipment theory is complete.
Show identity and composite interface-change coherence. For a global family
f_i:X'_i->X_i, describe the induced base-changing map explicitly; for maps
chosen separately at occurrences require agreement wherever substitution glues.
In particular, when a nullary child contracts a loop slot, the two primed
boundary sets and their maps must coincide; merely equal unprimed labels
with independently chosen boundary maps are insufficient.

T4. Supply a genuine bridge to the existing public A API, not merely a separate
untyped implementation: X family -> relation quiver -> Component; typed path
-> exact same Path/Slot occurrences; operations totalized over path fibres;
identity/subst/profile laws -> CalcData/Calc fields with full equality transport;
strict inclusion exact -> containment; primitive assignments preserving every
profile and whole -> A2 unique free extension. Either construct an actual Lean
Calc or provide a rigorous written two-sided correspondence with every map,
direction, law and assumption explicit. Finite C tests independently exercise
profile order, repeated positions, grouping and nullaries. No syntax equality
is inferred from semantic equality; no quotient by the selected model's kernel
is silently introduced. Distinct primitive labels and distinct groupings may
map to the same relational cell, but raw syntax remains distinct.

## Finite certificate domains, frozen before attempt

F1. Exhaustive binary composition/restriction domain:
|A|,|B|,|C|,|A'|,|B'|,|C'| in {0,1,2}; all functions f,g,h of those sizes;
all R subseteq A x B and S subseteq B x C. Check inclusion, comparison
realizer map, equality when g is onto, containment-cell survival and the exact
vs nonexact distinction. Endpoints empty cases are retained. No random sampling.
F2. Exhaustive associativity domain: each of four interface cardinalities in
{0,1,2}; all relation triples; all identities including zero-sized sets. Check
associativity and both relation units by two independently written evaluators.
F3. All paths of arity 0 through 3 with interface sizes in {0,1,2}, all relations,
and all contiguous segmentations, including empty segments, with outer arity
0 through 3. For each segmentation q_i choose EVERY R_i containing C(q_i),
then EVERY W containing C(R_1,...,R_k), and check flattened containment.
For exact choices all those inclusions are equalities; check exact closure.
Every empty segment is at the SAME interface label at both ends (a loop),
not merely interfaces of equal cardinality.
If factorization avoids repeating equivalent cases, document an exact coverage
bijection and independently check it; do not quietly truncate the domain.
F4. Principal named certificate uses distinct interface labels A,B,C with
cardinalities 2,3,2, a nonempty composite and a larger nonexact whole. B' has
cardinality 2 and embeds non-surjectively in B; choose relations such that
restriction removes at least one realizable outer pair while retaining another.
The original exact cell then restricts to a surviving containment but NONEXACT
cell. Include a positive surjective comparison with a genuinely many-to-one
internal map; include endpoint noninjectivity and all relevant empty-set cases.
F5. Mixed typed four-leaf path with repeated literally identical loop relation
occurrences at B, different valid occurrence substitutions, and two different
binary grouping trees evaluating to the same relational cell. Two primitive
labels with same profile/whole remain distinct in syntax. Include explicit
nullary loop containment (Delta<=W), exact nullary (W=Delta), and a noninjective
nullary restriction failing exactness. Wrong endpoints/order/wrong repeated
occurrence and false equality must be rejected by negative controls.
F6. Deliberate mutations (at minimum reverse containment, conflate pull-of-
composite with composite-of-pulls, and identify repeated occurrences) must be
detected. Independent checker must compute rather than echo author certificates.

## Evidence, limits, review and cheap-shortcut exclusion

P supplies all-parameter T1--T4 and proofs with empty/nullary cases. C supplies
F1--F6, exact domain counts, deterministic source, results and independent
redundant computation. Optional L is explicitly delimited and audited, not a
substitute for full P. Non-author mathematical and clean-reproduction review
must inspect actual source and arguments, report correctness separately from
scientific scope, and disclose agent/correlated-model limitations. Parent owns
acceptance and Library delivery. Source checkpoint and human report (.txt)
will list all gaps, failed strategies, axioms, finite domains and instructions.

Cheapest tempting solution: predicate relations plus an elementary non-surjective
binary example. It does NOT pass by itself: T2 requires all profiles and actual
substitution, T3 actual coherent maps (including n=0 kernel-pair comparison),
T4 public A correspondence, F1--F6 independently checked nontrivial certificates,
and full C2 later requires D2/E use. Other excluded shortcuts: only singleton
interfaces; definitional W=C(p); finite testing as universal proof; all semantic
equalities declared syntax equations; surjectivity-free exact transport; empty
profiles treated as empty relation instead of diagonal; using same component
type to merge occurrences; asserting every boundary change is a same-base Calc
morphism. No novelty is claimed for relations, existential composition, or these
standard elementary laws. This is infrastructure supporting future D2/E, not a
standalone major research contribution and not acceptance of full C2.
