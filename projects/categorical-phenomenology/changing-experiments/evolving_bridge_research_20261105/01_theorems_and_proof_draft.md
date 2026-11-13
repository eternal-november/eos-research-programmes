# Operational interface growth: theorem and proof draft

## 1. Source and generated experiment doctrine

Let C be a small category of actual deterministic native programs and X:C→Set its state semantics. For each interface i supply seed experiment columns E_i⊆P(X_i). Each seed carries a native observation witness. Define G_i={X(p)^−1(C): p:i→j, C∈E_j}. This is the least contravariantly stable family containing the seeds. Native words/programs remain annotations; equal columns may be identified semantically but no execution witness is inferred from equality alone.

Set M_i={intersections of arbitrary families of G_i}, including X_i as the empty intersection. This is a complete meet lattice of extents. Inverse image along a native program p restricts to p*:M_j→M_i and preserves all meets. Therefore it has left adjoint p_!(A)=cl_j(X(p)[A]); identities/composition hold. Object markings γ_i(x)=cl_i({x}) form a join-dense generating set, and p_!γ_i(x)=γ_j(X(p)x). Define Q_i as row equality for G_i; it is a quotient functor on C. These are the same source operations in two native characterization categories, not separately selected maps.

## 2. Least simultaneous repair theorem

Let E⊆E+ and C⊆C+ have the same state objects and compatible source semantics on common arrows. On old objects G⊆G+ and M⊆M+. The finer state quotient has the unique surjection ρ_Q:Q+→Q with ρ_Q q+=q. The extent inclusion j:M→M+ preserves arbitrary meets; its left adjoint is ρ_M(A)=cl_old(A), a surjective complete-join map satisfying ρ_M γ+(x)=γ(x). For every shared native operation p,

ρ_M,j p_!+ = p_! ρ_M,i.

Proof: inclusions commute exactly with inverse images, and take left adjoints. Equivalently cl_old(cl_new(pA))=cl_old(p cl_old(A)), using old operational stability. This comparison is forced, not assumed. It is transitive for successive interface changes.

Minimality: M+ is the least Moore family extending old M and new seeds for which every operation of the enlarged native category, including old operations acting on new extents, has an object-marking-compatible complete-join action. Indeed such an action exists iff inverse images of all extents are extents (fixed-context extension criterion); induction on native words plus meet closure forces M+ into every admissible family. Q+ is independently the coarsest enlarged-category-operation congruence refining the old row equivalence and the added seed distinctions. Thus FCA repair may be strictly stronger than state repair.

## 3. Three distinct exactness tests

For a finite carrier X, old generated columns F, the entire resulting operation set A (old and new), plus new seeds N, write F+=Gen_A(F∪N). The three comparisons are unchanged exactly as follows.

- States: each added seed is constant on old row classes, and every primitive operation respects old row equality.
- Full FCA: every added seed is an old extent, and every primitive inverse image of each old extent is an old extent. It suffices to check old generating columns, since inverse images preserve intersections.
- Object nerve as a simplicial complex: every added seed and every primitive inverse image of an old column is contained in some old column (ignore the empty column when the old family is empty). This is equivalent to stability of the downward closure of columns.

The state criterion is weaker than FCA. Neither alone determines topology: topological support remembers actual common experiments, not just semantic empty intersections. Equal homotopy types can occur despite unequal complexes; the stated topological criterion is strict equality, not a homotopy equivalence criterion.

## 4. Wiring and derived commutation

Let P⊆X×Y be the actual compatible-state carrier. Its local column family is the pullback of completed component experiments along π_X and π_Y. Its extent family is precisely the restricted rectangles P∩(A×B), A∈M_X,B∈M_Y. Assume component words lift to admitted joint native words (check this, do not infer it from semantic endpoint maps). Then the full joint completion contains the local family, so the comparison directions in §2 follow.

Completion commutes with this wiring at the FCA level iff every admitted joint primitive pulls every closed rectangle back to a closed rectangle (and added joint seeds are rectangles). Equivalently check the two sorts of generating cylinders. State-level commutation only asks that each joint primitive descend to the realizable image of the local quotient profile. This is strictly weaker. A product formula holds when joint operations are genuinely componentwise and independent component operations lift. Shared resources belong in P and can invalidate liftability.

## 5. CNOT witness, fully closed under all allowed words

Take X=Y={0,1}, P=X×Y, with four local observations x=0,x=1,y=0,y=1. Initial operations are identity only. Each component is fully observed. The four local columns are the four edges of a square. There are 4 predictive rows, 10 full FCA extents (empty, four singleton vertices, four edges, full carrier), and Betti numbers (1,1,0,0) over F2.

Add actual native CNOT T(x,y)=(x,x⊕y). It is involutive, so all words are 1 or T. Its inverse images add exactly the two diagonal columns x⊕y=0 and x⊕y=1. There remain four states, but 12 extents and the nerve is the one-dimensional complete graph K4, Betti (1,3,0,0). The old marked concept action is obstructed: the diagonal U={00,11} has old closure P, but T(U)={00,10} is an old proper column. Therefore no join-preserving old-lattice action can agree with T on the marked states. The new lattice is the least repair supporting it.

Add native reset R(x,y)=(x,0). Closing under all mixed CNOT/reset words adds exactly ∅ and P, no other columns: every possible observation is one of x=0, x=1, y=0, y=1, x⊕y=0, x⊕y=1, false, true. Preimages of this 8-column family under both maps remain in the family (checked exhaustively). Hence rows and FCA stay unchanged (4 and 12), but the universal experiment makes the nerve the full 3-simplex, Betti (1,0,0,0). This latter phenomenon is already in the prior project; the added content here is deriving it from native operation closure and isolating its interaction with the first, FCA-only repair.

## 6. Noncommuting interface changes

A one-pass completion under B and then A need not support B after A has introduced a new test. Exact finite example on states {0,1,2,3}, seed {1}, maps a=(0,0,0,1), b=(0,0,3,0). Gen_B followed by Gen_A gives columns ∅,{1},{3} and merges 0 with 2. Full {a,b}-word closure also has {2}, witnessed by execute b then a then observe {1}. Thus a newly obtained test makes a formerly silent operation informative. Alternating to the least common fixed point is essential; it is not correct to complete each change once independently.

## Checks already persisted

check_evolving_incidence.py and check_results.json verify all CNOT/reset mixed-word closures, counts, native words, and mod-2 homology. Exhaustive checks over every distinct-column context on ≤3 objects and every total unary operation: 6,980 cases, 20,940 exactness comparisons, 173,796 action/refinement square checks. These are computational sanity checks, not a substitute for proofs. Search for the noncommutation witness explicitly includes all maps on ≤3 states before finding a 4-state witness for one seed; no global minimality claim beyond that search scope.
