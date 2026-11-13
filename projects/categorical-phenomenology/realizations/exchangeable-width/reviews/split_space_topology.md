# Split stochastic pair topology: direct good-cover proof

Let D_{p,k} consist of row-stochastic nonnegative p-by-k matrices with pairwise disjoint row supports. Let S_{p,k} consist of row-stochastic nonnegative pairs (Q,L), of sizes p-by-k and k-by-p, with QL=I_p. Projection pi(Q,L)=Q lands in D_{p,k}. Indeed, Q_{ij}>0 forces L_{j,*}=e_i, so no column can occur in two row supports. Conversely any Q in D admits at least one decoder.

## Good cover theorem

The projection pi:S_{p,k}->D_{p,k} is a homotopy equivalence for all k>=p.

Proof. Index a finite open cover by injections a:[p]->[k]. Put U_a={Q:Q_{i,a(i)}>0 for all i}, and V_a=pi^{-1}(U_a). These cover D and S respectively. For a finite nonempty collection F of injections, set A_i={a(i):a in F}. Its intersection is nonempty exactly when the sets A_i are pairwise disjoint.

In that case define Q^F to give weight 1/|A_i| to each column in A_i in row i, and zero elsewhere. The homotopy Q_t=(1-t)Q+tQ^F remains in the intersection of the U_a: every column in A_i already belongs exclusively to row i; all other columns only lose mass. It contracts this intersection to Q^F.

For (Q,L) in the corresponding V intersection, every decoder row indexed by A_i is necessarily e_i. Thus ((1-t)Q+tQ^F,L) remains a split pair throughout, since both QL=I and Q^F L=I. At its endpoint, all rows of L outside the union of A_i are unconstrained. Contract these rows linearly to a fixed probability vector b, leaving rows in A_i equal to e_i. This contracts the entire intersection in S. Consequently both covers are good covers with exactly the same nerve. Naturality of the nerve lemma identifies pi with the identity on that nerve up to homotopy, and proves the theorem.

This argument does not claim that pi has a continuous section. Vacant decoder rows can obstruct an exact section over a prescribed Q, but do not obstruct homotopy lifting/existence up to changing Q.

## Equivariance

All covers and the projection are equivariant under permutation of the p colors. A nonidentity permutation cannot stabilize a nonempty simplex of the common nerve: an injection and its color-permuted version would impose two different colors on one column. Thus the induced action on the nerve is free. Equivariant nerve-lemma constructions (choose partitions of unity equivariantly and contractions on orbit representatives) also give equivariant homotopy equivalences. Equivalently one may use the ordinary equivalence for connectivity and the explicit free-CW extension argument below, avoiding any dependence on the equivariant nerve lemma.

## Moore-space consequence for p=3

Take X=M(Z/3,1), the 2-dimensional CW complex formed by attaching one disk to a circle by degree 3, and its connected principal C3 cover E. Given the standard fact that D_{3,5} is simply connected, S_{3,5} is nonempty, path-connected and simply connected by the theorem. There exists a C3-equivariant map E->S_{3,5}: choose the value on one representative of each free 0-cell orbit, extend over representatives of 1-cell orbits using path-connectivity, and extend over representatives of 2-cell orbits using simple connectivity; transport all choices by C3. There are no higher cells. Hence the associated bundle E x_{C3} S_{3,5}->X has a section. This gives genuinely continuous Q and L in local component frames, not merely a deleted-product Q-map.

Equivalently, choose s in S and a path gamma from s to g.s. Its three translates concatenate into the attaching loop gamma*(g.gamma)*(g^2.gamma). This loop is nullhomotopic in S_{3,5}, so fill it and translate that filling to the other lifted 2-cells.

For k=4, D_{3,4} is a graph and the C3 action is free. If a C3-equivariant E->S_{3,4} existed, composing with pi would give an equivariant E->D_{3,4}. The induced X->D_{3,4}/C3 would pull back the graph's principal cover to E. But pi_1(X)=Z/3 has no nontrivial homomorphism to the free group pi_1(D_{3,4}/C3), so its pulled-back cover is trivial, a contradiction. Thus split-pair width for this cover is exactly 5 (provided the base family realizes this cover).

No claim here converts an arbitrary nonnegative HMM realization into a split pair; that is a separate lower-bound problem.
