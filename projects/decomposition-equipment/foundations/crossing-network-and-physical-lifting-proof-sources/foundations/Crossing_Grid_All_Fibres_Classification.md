# Complete realization groupoid for crossing grids with empty fibres

## Plain language summary

The visible crossing-grid theorem gives a direct test when every surrounding component exposes the missing component. Empty fibres change the answer: some matching choices are no longer determined, and some intermediate witnesses can become completely invisible. This note closes those cases without deleting them.

Every intermediate witness that appears in either supplied parent factorization has a finite bound on its possible multiplicity. We can therefore enumerate its typed matching data and test the actual whole-witness equation. Relabelling those intermediate witnesses identifies equivalent realizations and has no nontrivial stabilizers. The remaining witnesses, unseen by both parent factorizations, are arbitrary finite sets and retain their actual permutation symmetries.

The result is a complete presentation of the realization groupoid and an end-to-end existence procedure for the four-component schema, including empty object sets and an empty parallel component. It is a finite enumeration theorem for the bounded part, not a claim that exhaustive enumeration is efficient or that the visible holonomy algorithm extends unchanged to all empty cases.

## 1 The fixed four-component problem

Fix arbitrary finite object sets A,B,C,D,K,L and finite spans

    R:A↝B,   Q:K↝L,   S:C×L↝D,
    P:A↝C,   N:B×L↝D,

together with a specified whole-witness isomorphism

    θ:(P×Q);S ≅ (R×Q);N.                              (1)

No nonemptiness or visibility assumptions are imposed. The unknown is a finite span T:B↝C with actual isomorphisms

    α0:R;T ≅ P,
    β:(T×id_L);S ≅ N                                  (2)

satisfying, for every composable r,t,q,s,

    θ((α0(r,t),q),s)=((r,q),β((t,l),s)),               (3)

where l is the output of q. Morphisms are bijections of T over B,C preserving α0 and β. Denote this groupoid by GridSol(θ).

An optional prescribed abstract relation Tbar⊆B×C requires support(T)=Tbar exactly. Without such a prescription all supports are allowed. Giving a support condition does not identify different intermediate witnesses with the same endpoint pair.

Write R_ab for witnesses of R from a to b, P_ac for witnesses of P from a to c, S_(c,l),d for witnesses of S from (c,l) to d, and N_(b,l),d for witnesses of N from (b,l) to d. Write R_b for the union over a, and S_c^all for the union of S_(c,l),d over all l,d.

## 2 Bounded and invisible endpoint pairs

Partition B×C into

    J = {(b,c): R_b≠∅ or S_c^all≠∅},
    I = {(b,c): R_b=∅ and S_c^all=∅}.                 (4)

A pair in J is visible to at least one parent isomorphism in (2), even if Q is empty and the whole equation (3) has no witnesses. A pair in I is invisible to both parent isomorphisms.

For a realization let n_bc=|T_bc|. The two parent isomorphisms imply the equations

    Σ_b |R_ab| n_bc = |P_ac|             for every a,c,    (5)
    Σ_c n_bc |S_(c,l),d| = |N_(b,l),d|  for every b,l,d.  (6)

Every coefficient of a variable n_bc with (b,c)∈I is zero, so these variables do not occur effectively in (5),(6).

For (b,c)∈J define an explicit finite upper bound M_bc as the minimum of the following nonempty finite collection of integers:

    floor(|P_ac|/|R_ab|) for every a with |R_ab|>0;
    floor(|N_(b,l),d|/|S_(c,l),d|)
        for every l,d with |S_(c,l),d|>0.              (7)

At least one denominator is positive by the definition of J. Every solution satisfies 0≤n_bc≤M_bc, because each relevant summand is nonnegative and is bounded by the corresponding right side of its equation.

Let Count be the finite set of vectors n=(n_bc)_(b,c)∈J within these bounds satisfying all equations (5),(6), with n_bc interpreted as zero on I. In the prescribed-support version also require n_bc>0 exactly for the pairs of J belonging to Tbar. Zero-coefficient equations with a nonzero right side make Count empty; they are not discarded.

## 3 The finite typed matching sets

For n∈Count take the standard labelled bounded span

    T_n = coproduct_{(b,c)∈J} {(b,c)}×[n_bc],

where [0]=∅. Its fibres on I are empty.

Let A_n be the finite set of all typed bijections α0:R;T_n≅P. Explicitly,

    A_n = product_(a,c)
          Bij(coproduct_b R_ab×[n_bc], P_ac).          (8)

Let B_n be the finite set of all typed bijections β:(T_n×id_L);S≅N. Explicitly,

    B_n = product_(b,l,d)
          Bij(coproduct_c [n_bc]×S_(c,l),d,
              N_(b,l),d).                            (9)

The equations defining Count ensure that corresponding source and target sets in (8),(9) have equal finite cardinalities. Empty products and the unique empty bijection are used literally.

Define Z_n⊆A_n×B_n by imposing (3) for every composable tuple r,t,q,s. This is an explicit finite check using the supplied θ. In particular, if Q=∅ the check is vacuous, but the two typed bijections (8),(9) remain mandatory.

Let

    G_n = product_(b,c)∈J Sym(n_bc).

It acts on T_n by fibrewise relabelling and on matching pairs by

    (g·α0)(r,t)=α0(r,g^{-1}t),
    (g·β)((t,l),s)=β((g^{-1}t,l),s).                  (10)

Equation (3) is preserved by this action, since replacing t by g^{-1}t gives the same equation.

### Lemma 1 The bounded action is free

The action of G_n on Z_n is free.

Proof. Suppose g fixes a matching pair. Fix t∈(T_n)_bc. If R_b≠∅, choose r∈R_b. Equation (10) and injectivity of α0 imply g^{-1}t=t. If R_b=∅, membership in J guarantees some l,d,s∈S_(c,l),d. Equation (10) and injectivity of β again imply g^{-1}t=t. Thus g fixes every t and is identity. The proof does not use Q or any whole witness. ∎

Consequently the finite action groupoid Z_n//G_n is equivalent to the discrete set of its orbits Z_n/G_n. Different orbits are genuine nonisomorphic bounded realizations. There are |Z_n|/|G_n| orbits, with the empty-set case interpreted as zero.

## 4 The complete groupoid classification

For (b,c)∈I let F_bc be the groupoid of permitted finite sets in that fibre:

- without a support prescription, F_bc=FinSet_iso;
- if (b,c)∈Tbar, F_bc=FinSet_nonempty,iso;
- if (b,c)∉Tbar, F_bc is the terminal groupoid containing only the empty set.

Here FinSet_iso is equivalent to the disjoint union over n≥0 of B Sym(n); its nonempty version uses n≥1. These automorphisms permute actual invisible intermediate witnesses.

### Theorem 2 Complete crossing-grid realization groupoid

For arbitrary finite input data (1), with or without the stated support prescription,

    GridSol(θ) ≃
      (coproduct_(n∈Count) Z_n//G_n)
      × (product_(b,c)∈I F_bc).                      (11)

Equivalently the first factor can be replaced by the finite discrete set coproduct_n Z_n/G_n. The second factor is the entire, explicitly identified unbounded part.

#### Proof from a realization to the presentation

Split T into its endpoint fibres on J and I. On J its cardinalities obey (5),(6) and the bounds (7), hence define n∈Count. Choose fibrewise bijections from the standard labelled span T_n to T|J. Transport α0 and β across those bijections. Fibres on I contribute no witnesses to either source in (2), because R_b and every S_(c,l),d are empty. Therefore the transported maps are exactly an element of A_n×B_n. Its coherence equation is (3), so it belongs to Z_n.

Changing the chosen labels acts exactly by G_n. Any realization isomorphism preserves all endpoint fibres and their cardinalities; on the J part it is precisely a relabelling intertwining the two matching pairs. On each I fibre it is an arbitrary bijection of the invisible finite sets, with no additional equation from α0,β, or θ. Thus all objects and all morphisms are represented on the right side of (11).

#### Proof from the presentation to a realization

Take n, a pair (α0,β)∈Z_n, and arbitrary permitted finite sets E_bc on I. Form T as the disjoint union of T_n and those invisible fibres. Since the invisible fibres contribute no source witnesses to either map in (2), the original α0 and β extend uniquely to isomorphisms with this larger T. They satisfy (3): a composable tuple containing t in an I fibre cannot exist, because it would require both r∈R_b and s∈S_c^all. For the bounded fibres, (3) was checked in Z_n. The support filter holds by construction.

The relabelling and invisible-set bijections give exactly the realization morphisms. These constructions are mutually inverse up to the chosen standard fibre labels and their canonical isomorphisms, proving the equivalence. ∎

### Corollary 3 Existence is decidable end to end

A realization exists iff Z_n is nonempty for at least one n∈Count. Each allowed invisible fibre has at least one permitted choice: empty when allowed, singleton when positive support is required. Therefore invisible fibres introduce no additional existence obstruction.

An explicit terminating procedure is: compute I,J and the bounds; enumerate Count; enumerate the typed bijections (8),(9); test (3). A successful pair and any permitted invisible sets are a complete positive certificate. This is not claimed to be an efficient algorithm; the typed matching enumeration can be factorially large.

The source theorem does not replace the sharper labelled-rectangle, holonomy, and cylinder criteria under full visibility. It provides the complete fallback presentation when those hypotheses fail.

## 5 Empty cases and genuine nonuniqueness

### An empty parallel component does not erase the parent equations

Let all object sets be singletons, Q=∅, R=∅, P a singleton, and S=N=∅. Both sides of (1) are empty and θ is their unique isomorphism. Nevertheless no realization exists, since R;T is always empty and cannot be isomorphic to P. Equation (5), with zero left side and positive right side, detects this. Testing only whole witnesses would give the wrong answer.

### Two different bounded realizations with no automorphisms

Let all object sets be singletons, R and S singletons, Q=∅, and P,N each two-element sets. Then n=2 is forced, A_n and B_n each have two bijections, and all four pairs satisfy the vacuous whole equation. The group Sym(2) acts freely, leaving two orbits. They correspond to the two actual matchings between the named P and N witnesses. These are genuine nonisomorphic realizations, not extra labels attached to one solution.

### Completely invisible witnesses retain their symmetries

Let all object sets be singletons and R=S=P=N=∅. Q may be empty or nonempty. The only endpoint pair lies in I, and all visible matching data are uniquely empty. Thus GridSol(θ)≃FinSet_iso, or its positive/zero support restriction. A fibre of n invisible witnesses has automorphism group Sym(n).

### Empty L, B, or C

If L=∅, Q,S,N are empty by typing. Equations (6) and coherence (3) are vacuous; α0:R;T≅P is still required. The theorem reduces to its typed tiling classification, with ghost fibres exactly those for which R_b is empty.

If B=∅ then T is necessarily empty and equation (5) requires P=∅. If C=∅ then T and P are empty, and equation (6) requires N=∅ whenever its typed endpoint set permits witnesses. These consequences remain valid even if Q is empty, so (1) alone does not expose the failure. All empty-index products, sums, and matching sets in (11) give these results directly.

## 6 Compatibility with the existing transport theorem

The outer-context transport formulas for crossing grids use only the isomorphisms α0,β and the coherence equation (3), not visibility. Hence every realization classified by (11) transports under arbitrary outer whiskering with the same T, and the tuple formulas retain their associativity and unit coherence.

Such transport need not preserve the decomposition into J and I. A previously visible fibre can become invisible after a context deletes all its exposing witnesses, acquiring additional automorphisms in the target problem. Thus transport is a functor on full realization groupoids, not generally an equivalence or a bijection on orbit sets.

## 7 Scope and status

Theorem 2 classifies the complete realization groupoid of this specified four-component crossing schema, including support-constrained fibres, empty interfaces, nonunique bounded matchings, and genuinely invisible witnesses. It assumes the two parent components P,N and their actual matching θ are supplied. It does not classify arbitrary networks with several independently unknown components or physical implementation languages beyond finite spans.

The proof uses elementary finite cardinality equations, explicit bijections, and relabelling group actions. The bounded enumeration presentation is a completeness result, not a novelty claim for these mechanisms or an efficient replacement for the structural visible-case test.
