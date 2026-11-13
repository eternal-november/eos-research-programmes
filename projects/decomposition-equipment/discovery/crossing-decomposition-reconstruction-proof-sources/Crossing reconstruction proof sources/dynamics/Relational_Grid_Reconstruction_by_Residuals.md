# Relational grid reconstruction by residuals

## Plain language summary

For a fixed grid of open components, suppose one missing component must simultaneously reproduce several already specified larger components. If that missing component occurs once in each requirement, there is an exact synthesis procedure. First remove each candidate transition that would cause any forbidden parent behavior. Then check whether all required parent behaviors can still be produced. If so, the remaining transitions form the greatest solution, and every other solution is obtained by retaining enough of them to cover the requirements.

This reconstructs a missing implementation subject to multiple typed contraction equations, rather than merely showing that its final output can be computed. It also reveals a precise boundary: if an unknown component is copied and used twice in one requirement, the greatest-solution construction can fail.

The theorem concerns relational support. Preserving actual finite transition-witness sets and their prescribed bijections is a stronger span-reconstruction problem, addressed separately; it is not solved by Boolean support synthesis.

## 1 One unknown typed component

Let Y,Z be finite sets and let U subset Y x Z be unknown. For each k in a finite index set, let

  C_k : P(Y x Z) -> P(E_k)

be a map preserving arbitrary unions, including the empty union. It describes a fixed typed relational context with one occurrence of U. Relational composition with fixed components, product with fixed components, relabelling, and existential hiding all preserve unions in that occurrence. A composite of these operations does too.

Fix the required parent behaviors P_k subset E_k. For each candidate transition u in Y x Z, its image C_k({u}) is the set of parent behaviors that this single transition would produce in context k.

Define

  U_max = {u : C_k({u}) subset P_k for every k}.

### Theorem 1 Exact simultaneous reconstruction

The equations C_k(U)=P_k for all k admit a solution if and only if

  C_k(U_max)=P_k for all k.

When they do, U_max is the greatest solution under inclusion. The complete solution set is

  { U subset U_max : for every k and p in P_k,
      there is u in U with p in C_k({u}) }.

Proof. If U is a solution and u belongs to U, monotonicity gives C_k({u}) subset C_k(U)=P_k, so u belongs to U_max. Conversely, arbitrary-union preservation implies C_k(U_max)=union_{u in U_max} C_k({u}) subset P_k. Thus if any solution U exists, P_k=C_k(U) subset C_k(U_max) subset P_k, and equality holds. Finally a subset of U_max can produce no forbidden behavior, and the displayed coverage conditions say that it produces every required behavior. QED.

The test is explicit: it uses the primitive contexts on single transitions, not an assumed descent equivalence. It also describes all nonunique solutions. The inclusion ordering is meaningful here: smaller solutions remove allowed local nondeterministic transitions. It is not an isomorphism groupoid of finite spans.

### Obstruction presentation

Failure has a finite certificate: a required p in some P_k for which every candidate transition u capable of producing p also produces a forbidden behavior in some context j. Such a certificate contains the finite list of candidate u, the corresponding offending context j, and a point in C_j({u}) outside P_j.

Equivalently, each requirement has a set of safe producing transitions; reconstruction succeeds exactly when none of those producer sets is empty. Every solution is a hitting set for those producer sets, restricted to U_max. Different minimal solutions need not be comparable.

## 2 Explicit crossing grid equations

In the four-component crossing grid, let the fixed upper-left relation be R:A->Y, the fixed lower-left relation be Q:K->L, and the fixed lower-right relation be S:Z x L->D. The missing upper-right relation U:Y->Z must recover the parent top macro P:A->Z and parent right macro N:Y x L->D:

  U R = P,
  S (U x id_L) = N.

Assume the given left macro equals R x Q and the given bottom macro equals S(id_Z x Q). These are independent checks on the fixed parts. If the two missing-component equations hold, row and column assemblies give the same whole by relational associativity and product interchange.

For this grid,

  U_max = { (y,z) :
      for every a, a R y implies a P z,
      and for every l,d, (z,l) S d implies (y,l) N d }.

A conservative support-level grid completion exists exactly when

  U_max R = P,
  S (U_max x id_L) = N.

This is the two-sided relational residual, derived directly from the typed primitive contraction equations. It synthesizes every permitted middle relation rather than testing only the direct-image abstraction of a known concrete middle.

In Crossing_Grid_Conservative_Refinement_NoGo.md, the first equation alone fails. R sends a0 to y0 and a1 to y0,y1, whereas P sends a0 only to z1 and a1 only to z0. The candidate (y0,z1) is required by a0 but forbidden by a1. Thus no relation at all of the prescribed middle type can solve the contraction equations.

## 3 Compatibility with genuine surrounding contexts

Suppose U solves all equations. Apply any fixed union-preserving typed surrounding context D_k to each parent equation. Then

  D_k(C_k(U)) = D_k(P_k)

holds automatically. Therefore a conservative grid realization remains valid when the whole parent diagrams are inserted into the same fixed surrounding contexts. Iterated such substitutions are coherent because composition of the actual relation maps is associative.

The converse is false: a surrounding context can hide the behavior that distinguished a failure. Consequently the greatest synthesized solution for the transformed problem can be larger than the original U_max. Recomputing the residual after hiding is not the same as transporting the original greatest solution. Reflection holds when the family of surrounding maps reflects equality on the relevant attainable parent behaviors; an arbitrary existential hiding operation need not do so.

This is the correct limited contextual law. It does not say that replacing an internal interface by a quotient preserves composition. Wiring_Exactness_and_Joint_Abstraction.md gives explicit failures of that stronger assertion.

## 4 Internal interface reindexing

For clarity, take the simpler equations U R=P and S U=N, with R:A->Y and S:Z->D. Let maps

  h:A'->A, f:Y'->Y, g:Z'->Z, k:D'->D

reindex all four boundary sets. Define every primed relation by inverse image along its two corresponding endpoint maps; in particular U'(y',z') iff U(f(y'),g(z')).

There are always containments

  U' R' subset P',
  S' U' subset N'.

Equality in the first holds exactly when each (a',z') in P' has a matching original Y-witness in the image of f:

  exists y' : R(h(a'),f(y')) and U(f(y'),g(z')).

Equality in the second holds exactly when each (y',d') in N' has a matching original Z-witness in the image of g:

  exists z' : U(f(y'),g(z')) and S(g(z'),k(d')).

Thus surjectivity of f and g is sufficient to transport every original solution. Necessity is separate for each chosen internal map when tested against arbitrary other nonempty interface maps and external probes: a missing y or z can then be chosen as the sole matching intermediate witness. For a fixed simultaneous reindexing, surjectivity need not be necessary; for example Y' and Z' both empty can make both primed equations vacuous. The exact witness-cover conditions, rather than a blanket necessity claim, govern those degenerate cases. For a particular system, the displayed witness-cover conditions are weaker and exact.

This is an explicit interface-lifting condition, not a blanket assertion that all pullbacks preserve relational composition. It separates preservation of a supplied implementation from synthesis of potentially new implementations after reindexing.

## 5 Why repeated unknown occurrences change the problem

The one-occurrence/union-preservation hypothesis cannot be dropped. On {0,1,2}, let

  U1={(0,1)}, U2={(1,2)}.

Each satisfies U_i U_i=empty. Their union does not, because it has the two-step path 0->1->2. Hence the solution family of U U=empty has no greatest element containing both U1 and U2. In particular the union-of-safe-atoms construction is invalid for a context that copies U into two compositional occurrences.

Several unknown components, feedback, sharing of witnesses, or repeated unknown occurrences require further constraints. The theorem is a complete result for a single missing typed relation in union-linear contexts, not a solution of arbitrary network synthesis.

## 6 Mathematical baseline and status

Relational residuals, powerset adjoints and union-linear synthesis are standard order/relational algebra. The role of this proof is to specify and solve the exact support-level common-grid completion problem, expose its concrete obstruction certificates, and establish its genuine contextual and interface-transport limits. It must not be presented as discovery of residuation or as a substitute for the stronger witnessed square theorem.

The finite relations retain actual state values, and the companion path construction retains complete concrete state paths. Multiplicities of transition witnesses and prescribed bijections between parent whole realizations are additional data. Boolean feasibility can hold while finite-span witness reconstruction fails; any final integrated theorem must keep those layers distinct.
