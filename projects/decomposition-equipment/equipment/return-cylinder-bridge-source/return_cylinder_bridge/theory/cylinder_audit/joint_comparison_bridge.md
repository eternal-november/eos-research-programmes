# Bridge addendum: Boolean network semantics versus actual CFS middles

Status: one elementary obstruction theorem with its exact surviving comparison and boundary-interface law. No novelty claim. This concerns finite relational support/existence semantics, **not stochastic probabilities**. It connects the network calculation to the standard Set cylinder factorization, rather than proposing a new nearby reconstruction programme.

## 1. The model and the candidate comparison

Let R⊂P×X and S⊂X×T be two explicitly supplied primitive boundary relations. A preparation p and test t form an actual closed network whose observed Boolean outcome is

    A(p,t)=1 iff ∃x. R(p,x) and S(x,t).

This is computed from primitive incidence, not given as an independent global table. Let q:X→Q be a local observational quotient. Wiring the quotient primitives gives

    B(p,t)=1 iff ∃x,y. R(p,x), q(x)=q(y), S(y,t).

Thus A≤B, with no independence assumption. Encode either table as a Set cylinder: each preparation object is 1, each test object is 2, and the entry 1→2 is the table value. Its standard CFS middle is the row image

    M_A = { A(p,−) : p∈P } ⊂ 2^T,
    M_B = { B(p,−) : p∈P } ⊂ 2^T.

The E-cocone sends p to its row, and the M-cone evaluates a row at each test.

## 2. Obstruction theorem: kernel relaxation can realize every support inclusion

**Theorem.** For any finite Boolean tables A≤B on P×T, there are a finite internal interface X, a fixed local observational table on X with row quotient q, and primitive relations R,S as above such that their actual and quotient-wired outcomes are exactly A and B. Moreover, for fixed B the interface X, its local table, q, R, and BOTH reduced primitive relations can be held fixed while A ranges over all subrelations of B.

**Construction and proof.** Put E_B={(p,t):B(p,t)=1}. Let

    X=E_B×{0,1},       Q=E_B,       q(e,i)=e.

Give X local tests indexed by Q and observation

    L((e,i),d)=1 iff e=d.

Its equal-row classes are exactly the q-fibers. This remains true when Q is singleton; the empty case is vacuous. Define

    R(p,(e,i)) iff e=(p,t) for some t and i=0.

For e=(p,t), let S accept (e,0) at t when A(p,t)=1, and accept (e,1) at t when A(p,t)=0. There are no other S pairs. A genuine R/S cut has a common witness exactly for A=1. After applying q, every edge e in E_B has a reachable and an acceptable representative, so the quotient cut has support B. The reduced R relation depends only on the preparation endpoint of e, and the reduced S relation only on its test endpoint; neither depends on A. END.

This proves more than an isolated counterexample: local observational middles plus quotient primitive incidence leave **every subrelation of the predicted support** possible. Even giving the reduced primitive equations does not recover the actual joint cylinder. The missing information is alignment of primitive witnesses inside local equivalence fibers.

### Neither direction of preparation-compatible middle map is guaranteed

Take P={a,b,c}, T={t,u}, with rows

    A_a=00,  A_b=00,  A_c=10,
    B_a=10,  B_b=11,  B_c=10.

Entrywise A≤B, so the theorem realizes this by two primitive relational nodes and one local quotient cut.

A map h:M_A→M_B satisfying h(A_p)=B_p would send the common A-row of a,b to two distinct B-rows. No such map exists. Conversely a preparation-compatible map M_B→M_A would send the common B-row of a,c to two distinct A-rows. No such map exists either.

The exact conditions are respectively ker(row_A)⊆ker(row_B) and its reverse. Support inclusion implies neither. A map preserving BOTH the preparation legs and the original test legs would force A=B even before considering these kernel conditions.

Consequently the kernel-relaxed middle M_B, with its usual preparation and test legs, is **not an honest realization of the actual cylinder A** unless A=B. The earlier same-cylinder CFS realization-span lemma cannot be applied to it. This is a direct bridge obstruction, not a missing E/M preservation argument.

## 3. What comparison does exist?

There are two precise survivors.

### (a) An order-valued observation comparison

A≤B is a pointwise Boolean inequality with identity preparation and test boundaries. It is a valid order-lax pairing comparison if one explicitly uses a doctrine with inequality cells. It is not an ordinary Chu arrow or an equality-preserving Set-cylinder map.

The operational assurance is one-sided: an actual positive outcome is included in the relaxed possibilities, and an impossible relaxed outcome is impossible actually. A relaxed positive outcome need not be realizable.

### (b) A canonical common-refinement span of CFS middles

Form the combined-test cylinder with test set T⊔T, first copy evaluated by A and second by B. Its middle is

    M_AB = { (A_p,B_p) : p∈P } ⊂ M_A×M_B.

Projection yields

    M_A ← M_AB → M_B.

Both legs are surjections (E₀ maps), since they are restrictions of tests from the combined cylinder. The span is an honest CFS construction for this combined cylinder. Its image relation contains only pairs (u,v) with u≤v pointwise. It does **not** make M_B a realization of A or equate the same test on its two endpoints. It is distinct from the E-left/M-right mixed-corner span and the M-left/E-right same-cylinder realization span.

This apex can be represented symbolically as the quotient of preparation variables by equality of the two computed output functions; one need not print its full table. But its computation and size can be large. Merely naming this apex is not a compact reconstruction algorithm.

## 4. The exact primitive interface needed: fiber overlap, not global Eval

For each local class b∈Q, put X_b=q^-1(b), and define directly from the primitive equations

    U_(p,b)={x∈X_b : R(p,x)},
    V_(b,t)={x∈X_b : S(x,t)}.

Then the exact interface law is

    A(p,t)=∨_b [ U_(p,b) ∩ V_(b,t) ≠ ∅ ],              (1)
    B(p,t)=∨_b [ U_(p,b)≠∅ and V_(b,t)≠∅ ].           (2)

Equation (1) follows by partitioning the genuine witness x by q(x); (2) does the same for the two independently chosen witnesses. The reduced primitive relations retain only the two individual nonemptiness predicates in (2). They discard the overlap predicate in (1).

Therefore an exact symbolic interface may retain the U/V families or an overlap oracle/representation for the attainable families inside each fiber. Such an oracle is **local to a cut** and can be derived from primitive boundary constraints; it does not require supplying every already-composed closed experiment. A finite bitset representation is one direct implementation. More structured primitive equations may permit a smaller representation. No generic smaller representation follows from local observational collapse.

The exact additional law for support exactness is weaker than demanding every fiberwise overlap: whenever some class offers separately reachable/acceptable witnesses for (p,t), at least one class must offer an actual common witness. Requiring each nonempty U,V pair within every class to intersect is a sufficient local certificate, not a necessary global one; different classes can provide redundant witnesses.

This distinction avoids silently replacing existential support exactness by full witness lifting. It also exposes a concrete verification target for a given primitive interaction rather than assuming “adequate contexts.”

### Elementary lower bound against a universally tiny summary

Let one locally invisible fiber be X=[n]. Allow preparation primitives U_A=A for each subset A⊆[n] and singleton test primitives V_t={t}. Then actual observations are

    A(A,t)=1 iff t∈A.

All 2^n preparations have distinct joint rows, although the original local quotient of X has just one class. Any exact deterministic preparation summary through which all these singleton observations factor must distinguish all 2^n subsets: if two distinct subsets shared a summary, a singleton in their symmetric difference would distinguish them. Hence it requires at least 2^n states (or n bits in an unrestricted encoding).

This is not a claim that all instances are hard or that raw X must always be retained. It proves that no bounded-size reconstruction based only on the one local class can solve arbitrary admitted primitive interactions. The attainable boundary-incidence structure determines whether a compact sufficient interface exists.

## 5. Scope and conclusion

This completes a precise bridge in the finite relational model:

1. Primitive equations define the actual closed network and hence a Set cylinder.
2. Local quotient wiring defines a second Set cylinder with support overapproximation.
3. The overapproximation gives no canonical functional comparison of row-image middles in either direction.
4. A common-refinement span and an observation-order comparison do exist, with their exact meanings distinguished.
5. Exact composition needs primitive fiber-overlap information; the displayed interface law computes the needed semantics without postulating a global evaluation table.

Repeated cuts must preserve the same boundary-witness correlations. Independently replacing each intermediate family by nonemptiness loses them again. Algebraic cyclic feedback additionally requires simultaneous consistency around loops, as in the previous note. Neither support inclusion nor this finite Boolean argument supplies stochastic realization, causal guarded-feedback semantics, or a general physical implementation theorem.

All constructions here are elementary Boolean relational composition, image factorization, and quotient reasoning. The prior note lists the primary CFS/equipment sources; no newly discovered literature theorem or novelty is claimed here.

Nearest verified relation-lifting background: Bílková–Kurz–Petrişan–Velebil, [Relation lifting, with an application to the many-valued cover modality](https://arxiv.org/abs/1307.4682), characterizes functorial relation lifting using distributive laws or exact-square preservation; their [Relation Liftings on Preorders and Posets](https://arxiv.org/abs/1210.1433) gives the corresponding exact-lax-square account. These are established structural baselines, not results supplying the missing primitive fiber alignment in this example. The support calculation is not asserted novel.

For a multiport primitive the interface must retain its JOINT boundary relation; independent per-port feasible subsets can discard correlations before any cut. The one-cut overlap formula is not a license for that replacement. Symbolic conjunction of primitive joint constraints followed by equality gluing and existential elimination is exact, but gives no automatic compression bound.
