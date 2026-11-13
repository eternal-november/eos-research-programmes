# Decision complexity of witnessed crossing grid reconstruction

## Plain language summary

For explicitly listed finite witness data, the fully visible crossing-grid problem is decidable in polynomial time by the structural square and cylinder tests. Allowing empty exposing fibres changes the worst-case complexity: the complete problem is NP-complete, even when the support of the missing component is prescribed in advance and the parallel component is nonempty.

The hardness comes from choosing witness multiplicities in a degenerate case where one side exposes none of the missing witnesses. It is not a claim that the visible holonomy test is NP-hard. The result also does not apply automatically to succinct or circuit representations of the finite spans.

## 1 Explicit input model

Use the data and realization equations of Crossing_Grid_All_Fibres_Classification.md. Object sets, witness sets, all endpoint maps, the whole matching θ and the optional support relation Tbar are given as explicit finite lists and tables. The input size M counts their encoded lengths. Malformed data can be rejected by checking types, bijectivity and endpoints in polynomial time.

The decision problem asks whether any finite T,α0,β realizing the supplied grid exists, optionally with support(T)=Tbar. The unknown cardinality of T is not part of the input.

## 2 Polynomial certificate bound

### Lemma 1 Small realizing component

If an instance is realizable, it has a realization with

    |T| ≤ |P| + |N| + |B||C|.                         (1)

Without a support prescription the last term can be omitted.

Proof. Split the endpoint pairs into J and I as in the all-fibres classification. For every t with R_b nonempty choose one fixed r_b∈R_b. The map t↦α0(r_b,t) is injective into P, because the source pairs are distinct and α0 is injective. Thus at most |P| witnesses of T lie over such b.

For every remaining visible t, R_b is empty but S_c^all is nonempty. Choose one fixed l_c,d_c,s_c∈S_(c,l_c),d_c. The map t↦β((t,l_c),s_c) is injective into N, so there are at most |N| such witnesses.

Invisible fibres affect neither α0 nor β nor whole coherence. Remove all their witnesses when support is unprescribed. With prescribed support, keep one witness for each required invisible endpoint pair and none for a forbidden pair. There are at most |B||C| pairs. These changes preserve the realization equations. ∎

### Proposition 2 Membership in NP

The general decision problem, both with and without prescribed support, belongs to NP.

Proof. Guess a T satisfying (1), its endpoint maps, and the tables of α0 and β. Their source sets have sizes at most |R||T| and |T||S| respectively, hence polynomial in M. Verify typed bijectivity and the support condition. Enumerate all composable tuples r,t,q,s and check the actual equation (3) against the supplied θ table. Their number is at most |R||T||Q||S|, polynomial in M. Thus every yes instance has a polynomial certificate and polynomial verification procedure. ∎

## 3 NP hardness with prescribed support

We reduce from perfect three-dimensional matching, one of the NP-complete problems in Karp's original theorem. Equivalently, given three disjoint n-element sets X,Y,Z and a family B⊆X×Y×Z of triples, ask for a subfamily covering every element of X⊔Y⊔Z exactly once.

It is enough to use instances in which every universe element appears in at least one triple. An instance with an uncovered element is immediately negative and can be mapped to a fixed covered negative instance. For example, with two elements in each part, the three triples

    (x1,y1,z1), (x1,y2,z2), (x2,y1,z2)

cover every element but have no perfect matching. Thus this restriction does not remove NP-hardness.

Given a covered instance, put A=X⊔Y⊔Z and regard B as the set of triples. Take C,D,K,L to be singleton sets. Construct:

- R_ab has one witness exactly when a belongs to triple b, so every R_b has three witnesses.
- Q is the one-witness identity span between the singleton K and L.
- S and N are empty spans.
- P_a,c has deg(a)+1 distinct named witnesses, where deg(a) is the number of triples containing a.
- θ is the unique isomorphism between the two empty whole spans.
- Tbar=B×C, so every unknown multiplicity n_b=|T_b,c| is required to be positive.

This construction has polynomial size: |R|=3|B| and |P|=3|B|+|A|. The whole matching is explicitly empty, not omitted or inferred.

The β isomorphism and whole coherence are vacuous. Existence is exactly the existence of positive integers n_b satisfying

    Σ_(b containing a) n_b = deg(a)+1  for every a.    (2)

Set x_b=n_b−1≥0. Then (2) becomes

    Σ_(b containing a) x_b = 1  for every a.           (3)

Every triple is nonempty, so any x_b occurs in one of these nonnegative sums and is at most 1. Thus the x_b are Boolean choices, and (3) says precisely that the chosen triples form a perfect three-dimensional matching. Conversely a perfect matching gives n_b=1+x_b and hence typed bijections α0 by matching equal-sized A fibres.

The prescribed support conditions all pass at the support level: each a is covered by R, Tbar contains every b, and P has a positive fibre at every a. The hardness is in the witness multiplicities, not in a hidden support failure.

### Theorem 3 General NP completeness

The explicit finite crossing-grid realization problem with prescribed support is NP-complete. Hardness holds with Q a nonempty one-witness component, R_b nonempty for every b, L nonempty, and S=N empty. Thus among the visible-case hypotheses it is the S visibility requirement that fails in this reduction.

Proof. The reduction proves NP-hardness and Proposition 2 proves membership. ∎

Without prescribed support, NP-hardness follows from the same construction with |P_a,c|=1 and no positivity requirement: the nonnegative multiplicities n_b must then be 0 or 1 and encode an exact cover directly. Together with Proposition 2 this variant is NP-complete as well.

## 4 Polynomial decision in the fully visible regime

### Proposition 4 Fully visible crossing-grid decision is in P

Under the hypotheses of Crossing_Grid_Cylinder_Reconstruction.md, the realization decision problem, including prescribed support, is decidable in deterministic polynomial time in the explicit input length.

Proof. Materialize the interpolation boundary spans R×Q and P×Q; each has at most the product of two explicit witness-list sizes and hence polynomial size. The matching θ is already explicit. Build the labelled incidence diagram, check its rectangle conditions, and recover its connected-component filler. These are finite graph, label and bijection checks polynomial in the expanded data.

Then Test Q checks literal parallel-witness preservation in θ. Test F enumerates the canonical filler maps to record the finite descriptors, and Test L compares those finite descriptor sets. Their entries come from the already materialized finite span/composition tables, whose sizes are polynomial in M. Equality of prescribed support with the reconstructed descriptor span is another polynomial check. The cylinder reconstruction theorem proves these tests necessary and sufficient. ∎

No near-linear bound in the unexpanded grid input is asserted. Tensor products such as R×Q can be quadratically larger than their supplied factors, even when a whole composite is empty. This proposition establishes the polynomial-versus-NP-complete distinction, not an optimized runtime.

## 5 Source and scope

The NP-complete source problem is Karp's three-dimensional matching: Richard M. Karp, Reducibility Among Combinatorial Problems, in Complexity of Computer Computations, 1972, pp. 85–103, Main Theorem, problem 17. Publisher DOI: https://doi.org/10.1007/978-1-4684-2001-2_9 . An author-text reprint is available at https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Karp.pdf . The reduction above is supplied in full rather than assuming a complexity transfer from an informal analogy.

This theorem concerns one fixed four-component crossing schema and explicit finite witness inputs. It does not assert NP-completeness for the fully visible case, for every physical interface language, for arbitrary higher crossing networks, or for compressed representations. It is also not a counting-complexity classification of the full solution groupoid.
