# Wiring exactness and joint abstraction

## Plain language summary

A component may describe a boundary value only approximately. Two components can then appear to connect because their approximate values agree, even though they require different actual values. The resulting assembled behavior may be impossible. This is a different problem from whether one subsystem has enough observations to compute its own update.

The exact obstruction has a small presentation: a producer witness, a consumer witness, and an abstract boundary value agree at the coarse level but cannot be matched at the concrete level. For a chain of components, retaining the successive coarse values does not eliminate the problem. The set of still-possible concrete boundary values must also remain nonempty along the chain.

Two important consequences are proved below. First, two boundary simplifications can each preserve every behavior of the original system, yet introduce an impossible behavior when applied together. Second, there need not be a uniquely least informative safe repair of a boundary: two incomparable repairs may both work, while their common coarsening fails. Thus a canonical sufficient observation for a single update is not automatically a canonical repair for an assembled system.

These are elementary finite-relation/automata results used as a precise operational component of the crossing reconstruction program. They are not claimed as new general principles or as completion of that program.

## 1 Finite open components and interface abstraction

An open one-step component from a finite interface A to B is a relation R subset A x B. An element (a,b) of R is a concrete transition witness. For two components R:A->B and S:B->C, an actual assembled witness is a triple (a,b,c) with aRb and bSc. Their externally visible behavior is the relational composite SR.

A surjective abstraction q:B->Q forgets distinctions at the internal boundary. The separately abstracted components are

  R_q = {(a,z): exists b, aRb and q(b)=z},
  S_q = {(z,c): exists b, q(b)=z and bSc}.

An abstract assembled witness retains (a,z,c). It can be represented by independently chosen b and b' with aRb, q(b)=q(b')=z, and b'Sc. A concrete lift requires one shared b, not these two unrelated choices.

For each b, let L_b={a:aRb} and U_b={c:bSc}. For each z, put B_z=q^{-1}(z). Define

  Actual_z = union_{b in B_z} L_b x U_b,
  Apparent_z = (union_{b in B_z} L_b) x (union_{b in B_z} U_b).

There is always Actual_z subset Apparent_z.

### Theorem 1 Retained-middle exactness

The map from concrete assembled witnesses (a,b,c) to abstract assembled witnesses (a,q(b),c) is surjective if and only if

  Actual_z = Apparent_z for every z.

For each abstract witness (a,z,c), its exact realization set is

  Lift(a,z,c) = B_z intersection R[a] intersection S^{-1}[c].

It is not required to be a singleton. Empty Lift is the obstruction; a nonempty Lift retains all the genuine alternatives.

Proof. Membership in Apparent_z is exactly existence of independently selected producer and consumer witnesses with common q-value z. Membership in Actual_z is exactly existence of a shared concrete witness in that fibre. The displayed set lists those witnesses. QED.

This is a middle-amalgamation or rectangularity criterion derived directly from primitive composition. It is stronger than equality of externally visible endpoint relations, which may recover (a,c) using a concrete witness having a different q-value. It is weaker than retaining the originally chosen b and b' literally: that stronger demand requires b=b', not merely some lift.

## 2 Endpoint exactness has a complete compatibility presentation

Let E=SR. Define a reflexive symmetric relation C on B by

  b C b' iff L_b x U_b' subset E and L_b' x U_b subset E.

Let K_q be the kernel equivalence relation of q.

### Theorem 2 Safe quotient criterion

The abstraction q preserves the externally visible relation exactly,

  S_q R_q = SR,

if and only if K_q subset C.

Proof. An apparent endpoint pair is produced by some b,b' with b K_q b', a in L_b, c in U_b'. It is real iff (a,c) belongs to E. Quantifying these cross-pairs is precisely K_q subset C. The reverse cross-product is included because K_q is symmetric. QED.

Thus an endpoint obstruction is explicitly (b,b',a,c) with b K_q b', aRb, b'Sc and (a,c) not in SR. This theorem has no uniqueness hypothesis and no assumption that descent already holds.

### Corollary 2a No general coarsest safe quotient

Among all equivalence relations K subset C, there is a greatest one if and only if C is transitive. If it exists, it is C itself.

Proof. If C is transitive it is an equivalence relation and is greatest. Conversely, every compatible distinct pair b C b' generates the safe equivalence with the single nonsingleton class {b,b'}. Any greatest safe equivalence must contain every such pair, hence all of C, and therefore equal C. It must then be transitive. QED.

This is about externally visible endpoint exactness, not an arbitrary ordering of the full witness-preserving lift spaces.

### Example 2b Two incomparable repairs

Take A={a0,a1}, C={c0,c1}, B={0,1,2} with

  L_0={a0,a1}, U_0={c0},
  L_1={a0},    U_1={c0},
  L_2={a0},    U_2={c0,c1}.

The actual endpoint relation is {(a0,c0),(a1,c0),(a0,c1)}. The quotient with classes {0,1}|{2} is safe. The quotient {0}|{1,2} is safe. Both also satisfy Theorem 1. Any common coarsening merges all three values and introduces (a1,c1), which is impossible. No greatest safe quotient exists. Equivalently, starting with the one-value boundary, there is no unique least-information safe refinement.

This does not contradict the canonical least sufficient refinement of a fixed observation for one deterministic output. Here a boundary is used by two relational contexts, and the missing information concerns compatibility of their choices.

## 3 Independently safe abstractions need not be jointly safe

Let A={a0,a1}, B={b0,b1,b2}, C={c0,c1,c2}, D={d0,d1}. Consider the three-stage system

  R={(a0,b0),(a1,b1),(a1,b2)},
  T={(b0,c2),(b1,c1),(b2,c0)},
  S={(c0,d0),(c1,d1),(c2,d1)}.

Let q_B have classes {b0,b1}|{b2}, and q_C have classes {c0,c1}|{c2}.

### Theorem 3 Simultaneous abstraction failure

Either q_B or q_C alone preserves every externally visible behavior of STR, and each satisfies retained-middle exactness relative to the original concrete prefix and suffix. Applying both abstractions separately to the primitive components introduces the false endpoint pair (a0,d0).

Proof. The actual endpoint relation is

  E={(a0,d1),(a1,d0),(a1,d1)}.

For q_B, the merged B-class has predecessor set {a0,a1} and both of its members have suffix output set {d1}; hence its apparent and actual rectangles coincide. The singleton class is automatic. For q_C, the merged C-class has prefix predecessor set {a1}; its suffix outputs are {d0,d1}, each already realized. Again its rectangle is exact.

When both are applied, a0 reaches the coarse class of b0; the middle component can use b1 from that class and outputs c1; the final component can use c0 from the coarse class of c1 and output d0. There is no actual a0-to-d0 path: a0 forces b0, then c2, then d1. QED.

Consequently an exactness certificate relative to one concrete context cannot be silently reused after that context is abstracted. This example concerns actual component composition, not merely an observation-kernel inclusion on an unstructured state set.

The systems are finite open transition systems. R and S express nondeterministic choices, and T is deterministic. If desired, the nondeterministic relations can be implemented by deterministic components with hidden environment-choice inputs; existentially hiding those inputs gives exactly the displayed relations. This realization does not make the hidden inputs controlled by the subsystem. Repeating the one-step pipeline with an explicit reset yields a finite-state repeated system; the displayed false one-step behavior remains a false trace. No stochastic interpretation is asserted.

## 4 Full finite-path reconstruction

Let R_i subset X_{i-1} x X_i, i=1,...,n, and let q_i:X_i->Q_i be surjective for internal i=1,...,n-1. Set q_0 and q_n to identities. A retained abstract path is

  alpha=(x0,z1,...,z_{n-1},xn)

such that each pair of consecutive coarse values belongs to the separately abstracted R_i. Put F_0={x0}, F_n={xn}, and F_i=q_i^{-1}(z_i) internally.

Define the forward reachable sets

  P_0={x0},
  P_i=F_i intersection R_i[P_{i-1}].

### Theorem 4 Exact reconstruction and obstruction

The concrete lift set of alpha is precisely

  { (x0,x1,...,xn) : x_i in F_i and x_{i-1} R_i x_i for every i }.

It is nonempty if and only if xn belongs to P_n. If it is empty, the earliest index i with P_i empty is a finite obstruction certificate, consisting of the preceding nonempty reachability sets, the fixed abstract fibre F_i, and their failure to meet R_i[P_{i-1}].

Proof. Inductively P_i is exactly the set of possible ith concrete values of a lifted prefix. The terminal claim follows. The displayed path tuples retain every compatible sequence, so the construction does not choose one representative or identify different lifts. QED.

For a split at j, the full lift set is canonically the fibre product of the prefix-lift set and suffix-lift set over the ACTUAL interface X_j. The two successive fibre-product constructions for any three subpaths have the same tuples, hence the canonical reassociation bijections satisfy the pentagon and units. Replacing X_j by Q_j before taking the fibre product instead permits unequal concrete witnesses and need not reconstruct the same lift set; Theorems 1 and 3 quantify that failure.

This gives the correct witnessed substitution law in this relational specialization. It is standard fibre-product/path semantics, not an assertion that the general original equipment program has been completed. The path algorithm is a finite reconstruction procedure, not by itself a characterization of arbitrary crossing diagrams or an efficient bound for all networks.

## 5 Context dependence and the strongest unconditional limit

For a specified class of producer/consumer contexts through B, take the intersection C_* of the compatibility relations in Theorem 2. Then q is endpoint-exact in every allowed context if and only if K_q subset C_*. A coarsest such q exists if and only if C_* is transitive, by the same argument as Corollary 2a.

If all finite relations into and out of B are allowed, C_* is equality. Indeed for distinct b,b', choose singleton interfaces A={a},D={d}, producer {(a,b)} and consumer {(b',d)}. The actual composite is empty but q(b)=q(b') produces an abstract a-to-d behavior. Thus universally composition-exact surjective abstractions are bijective.

For a fixed finite typed primitive library, a bounded interface carrier family and contexts generated by relational composition, the complete set of endpoint relations of contexts is finite. It can be generated to saturation by finite relational composition. Testing Theorem 2 on all generated producer/consumer contexts is then an exact finite decision procedure. The claim is termination and exactness, not polynomial complexity. Restricting contexts is essential for meaningful noninjective abstractions, and a restricted context class must be justified by the permitted interfaces and operations rather than chosen merely to make a desired quotient safe.

## 6 Relation to the operation-sensitive state-context theorem

The companion operation-sensitive theorem concerns observation kernels under equivariant state-context maps of controlled deterministic systems. This note concerns existential abstraction under wiring of open relations. Neither property implies the other without additional hypotheses: the latter involves actual intermediate transition witnesses, not only pullback of state observations. In particular, the conjunction of Theorem 3's individually exact interfaces is not stable under further abstraction of the surrounding wiring context.

A full crossing reconstruction theorem should keep both obligations explicit. It must not replace the actual witness fibre product by an abstract one just because an observation-kernel criterion or an individual endpoint exactness test has passed.

## 7 Prior art and exact contribution of this note

The general phenomena of spurious abstract paths, finding the first nonrealizable prefix, and refining a partition are established abstraction-refinement material. Clarke, Grumberg, Jha, Lu and Veith explicitly describe these operations in *Counterexample-guided Abstraction Refinement*, including nonuniqueness and computational difficulty of choosing refinements:
https://www.cs.cmu.edu/~emc/papers/Conference%20Papers/Counterexample-guided%20Abstraction%20Refinement.pdf

Giacobazzi, Ranzato and Scozzari, *Making Abstract Interpretations Complete*, prove constructive results for complete extensions and restrictions of abstract domains under continuous semantic operations, and distinguish pointwise from fixpoint completeness:
https://www.sci.unich.it/~scozzari/paper/JACM00.pdf

The no-coarsest result here has narrower and different quantifiers: safe equivalence partitions of one interface for the specified producer and consumer, preserving that composite's endpoint relation. It does not refute complete-shell results over lattices of abstract domains. Theorems 1 and 4 retain the abstract middle/path labels and their full concrete lift sets, unlike bare endpoint equality; this distinction is useful for the program's witnessed semantics, not a claim that witness/path pullbacks are new.

The serial examples do not themselves constitute crossing decompositions of the whole. They isolate the horizontal-composition obstruction that a crossing reconstruction theorem must also control when its pieces are grafted into a surrounding system. They are supporting lemmas and counterexamples, not fulfillment of the promised crossing theorem.

## Status

Authored finite mathematical proofs and small executable checks accompany this note. No Lean verification, exhaustive classification of arbitrary finite-state networks, or novelty claim is made. The classification of safe equivalences in Theorem 2 and the explicit joint-abstraction failure provide concrete obligations for the larger reconstruction theorem; they do not substitute for that theorem.
