# What separate component observations do and do not determine

Research note, 4 November 2026. These are restricted results assembled from standard covering-space and mixture-identification arguments. No novelty or priority claim is made.

## 1. Declared model and what counts as identification

Let B be connected, locally path-connected and semilocally simply connected. Suppose separate observations have already identified two connected finite observable covers E_A -> B and E_B -> B, of degrees m and n, including their monodromy over the **same identified base and loops**. Knowing just their abstract monodromy groups is insufficient. Write X and Y for their fibers at b_0 and G = pi_1(B,b_0). Thus X and Y are known transitive finite G-sets.

A candidate reduced joint support is a finite cover J -> B with continuous maps to E_A and E_B over B, such that the ordered pair of component outputs separates the sheets of J. This injectivity is an explicit observable-state/minimality assumption. Without it, invisible extra sheets can change the latent cover without changing either component or even their joint output law. It does not identify a privileged physical mechanism.

The data equivalence relation is also explicit:

- With the component covers fixed, joint isomorphisms must commute with both output maps.
- If component isomorphisms are allowed, quotient by their deck automorphisms as well. This can identify candidates distinct under the first convention.
- An abstract joint-cover isomorphism that forgets its output maps is weaker still.

Statements below concern exact population laws. Finite-sample claims require the additional margins specified in Section 5. No joint tests, synchronized records, physical interventions, or latent-state access are inferred from marginal data.

## 2. Support classification and a positive marginal-only theorem

**Theorem 1 (reduced joint supports).** Under the assumptions above, the possible topological joint supports over the fixed component covers are exactly the nonempty unions of diagonal G-orbits in X x Y. Connected joint supports correspond to single orbits. Equivalently, they are the nonempty unions of connected components of the fiber product E_A x_B E_B.

**Proof.** A morphism of covers induces a G-equivariant map on fibers. The combined map J_(b_0) -> X x Y is injective, so its image is a G-invariant subset. Such subsets are exactly unions of orbits. Conversely, an invariant subset determines a subcover of the fiber product. Each nonempty orbit projects onto all of X and Y because those two G-sets are transitive. The monodromy action on J's fiber is transitive exactly when J is connected. This proves all claims.

**Probability feasibility qualification.** This is initially a classification of *topological candidates*. For specified, possibly nonuniform marginal probabilities, a candidate support must also admit coupling weights that are strictly positive on that support, zero off it, and have the specified row and column sums. For a family over B, these weights must satisfy the declared continuity or regularity requirements. Invariant subsets alone do not guarantee feasibility for arbitrary prescribed marginals. Under the invariant/uniform model of Theorem 2 below, every orbit and every nonempty union is feasible.

**Corollary 1 (coprime degrees force support).** If gcd(m,n)=1, the diagonal action on X x Y is transitive. Consequently, the only nonempty reduced joint support is the entire fiber product, regardless of whether the weights are flat.

**Proof.** Let O be an orbit. Its equivariant surjection onto X has equally sized fibers, so m divides |O|. Similarly n divides |O|. Coprimality implies mn divides |O|, but 0 < |O| <= mn. Hence O = X x Y. More generally, pairwise coprime component degrees force transitivity of a finite product by the same divisibility argument.

This is a genuine support-identification implication from complete separate observable covers **within this declared class**. It does not identify the joint probability law: full support is not independence. It also does not establish that the assumed covers, base-loop alignment, or support regularity are recoverable from the user's actual finite measurement access.

## 3. When the full joint law is identified

Call a probability assignment flat if transport along every path preserves its individual sheet weights. Mere continuity, smoothness, or analyticity is not flatness.

**Theorem 2 (flat coupling simplex).** Assume the joint probability assignment is flat and the component covers are connected. Let O_1,...,O_r be the diagonal G-orbits in X x Y, and let U_k be the probability matrix uniform on O_k and zero elsewhere. Then every flat joint law is uniquely

    W = sum_(k=1)^r lambda_k U_k,
    lambda_k >= 0, sum_k lambda_k = 1.

Every U_k has the same uniform X and Y marginals. Thus every lambda gives identical separate component laws, and the set of compatible flat joint laws is an (r-1)-simplex. In particular, the flat joint law is unique exactly when r=1; then it is the uniform product law. Its support is the union of the O_k with lambda_k>0.

**Proof.** Flatness makes W invariant under the diagonal G-action, hence constant on each orbit. Its total mass on O_k is lambda_k, giving the displayed formula and uniqueness. The projection of O_k onto X is an equivariant surjection between transitive G-sets, with constant fiber size. Its uniform probability therefore pushes forward to uniform probability on X, and similarly for Y. Conversely, each U_k is invariant and extends to a flat assignment on the associated subcover.

If the component marginals are nonuniform, this connected-cover flat model does not apply: a flat probability on a transitive finite fiber must be uniform. With disconnected component covers or other invariant constraints, the compatible weights instead form a linear-constraint polytope; the simplex conclusion cannot simply be reused.

### Flatness cannot be weakened to continuity

Let B=S^1, E_A={t in S^1: t^2=z} and E_B={s in S^1: s^3=z}. The fiber product is a connected six-sheeted cover. For |epsilon|<1/6, put

    w_z(t,s) = 1/6 + epsilon Re(t) Re(s).

These are globally well-defined positive continuous weights on the fiber product. The two square roots have real parts summing to zero, as do the three cube roots. Therefore the marginals are always 1/2 and 1/3, independent of epsilon. The supports and covers are identical, but the joint probability assignments differ. Thus coprimality determines support, while law uniqueness additionally requires flatness or some other identifying restriction.

### A counterexample that survives all relabelings

Take a base with two loop generators and let the component cover have monodromy generated by (12) and (123) on {1,2,3}. For example, this is a connected three-sheeted cover over a twice-punctured plane. Use two copies of this same component cover, with the same identified loop action. The diagonal product action has exactly two orbits:

    D = {(i,i): i=1,2,3},          |D|=3;
    O = {(i,j): i != j},          |O|=6.

Uniform probability on D and uniform probability on O give exactly the same uniform component laws, including separately held component readout histories and their monodromy. Yet their joint covers are connected and have different degrees, so they are not isomorphic even after forgetting labels and component maps. Each joint is reduced: its state is its ordered output pair. No invisible-state duplication is used. The natural S_3 component cover also has trivial deck group, since the centralizer of its permutation action is trivial.

A geometric realization is z -> z^3-3z, restricted over C minus {-2,2}. The two branch loops give distinct transpositions generating S_3. Complex roots, or categorical emission vectors obtained from them, provide multidimensional observable states. They should not be replaced by globally separated real Bernoulli biases: continuously ordered real numbers cannot exhibit this monodromy.

For circle covers of degrees m,n, there are gcd(m,n) orbits, each of length lcm(m,n). Different single-orbit choices are distinct over fixed component maps, but independent deck transformations permute them, and all are abstractly the same connected circle cover. Different numbers of included orbits give different total cover degrees. Accordingly, the S_3 example is stronger for demonstrating genuinely different connected structures.

## 4. What extra joint observations would identify the missing coupling

The following is an explicit additional experiment, not a consequence of access to marginal observations and not an intervention or causal-identification theorem.

Fix one regular basepoint or local chart. Suppose known component states i=1,...,m and j=1,...,n have bounded readout statistics T_A,T_B in [0,1], with distinct respective means p_i and q_j. On each trial, draw a latent pair (I,J) once from the unknown W and hold it fixed. Conditional on this pair, obtain independent A readouts with mean p_I and independent B readouts with mean q_J, with conditional independence also between the A and B readouts. Repeat trials independently.

Latent independence is **not** assumed: W may be any coupling. The conditional independence of the *emissions* and the held-pair protocol are assumed. Re-drawing the latent pair or combining unrelated runs changes the observed moments and invalidates the argument.

**Theorem 3 (finite observable inversion).** Define M_ab as the expectation of the product of a A statistics and b B statistics from the same held-pair trial, with an empty product equal to 1. For 0<=a<m and 0<=b<n,

    M_ab = sum_(i,j) w_ij p_i^a q_j^b.
    M = V_p W V_q^T,
    W = V_p^(-1) M V_q^(-T),

where (V_p)_(a,i)=p_i^a and (V_q)_(b,j)=q_j^b. The Vandermonde determinants are nonzero by distinctness. Hence this finite grid of population moments identifies W and its support up to the already admitted component relabelings.

**Proof.** Condition on (I,J). Conditional independence gives the product moment p_I^a q_J^b. Averaging gives the first identity. Matrix multiplication gives the second, and invertibility gives the third. One held trial containing m-1 A readouts and n-1 B readouts supplies bounded prefix-product estimators of the whole moment grid.

Separate moments M_a0 and M_0b depend only on the marginals, so separate measurements of arbitrary accuracy do not supply the mixed entries. With marginals already known, the grid has (m-1)(n-1) possibly informative mixed moments.

If the component emission laws are pairwise distinct, a bounded statistic with distinct means exists in principle: choose finitely many bounded tests distinguishing each pair and a generic linear combination, then rescale. This is not free experimental access. It must be computable from the admitted readout, and calibration or selection incurs a cost.

Assume an actual continuous joint-law family already exists, its positive support is locally constant in covering charts and forms the reduced support cover of Theorem 1, and the component monodromy is known. Then recovered support at one basepoint specifies its orbit union and therefore this joint observable support cover. The observation does not establish existence of such a global family, check probability feasibility at other basepoints, or identify its varying global weights. Flatness, if separately assumed, is what lets basepoint weights determine transported global weights. Without the support-cover promise, one basepoint says nothing about support changes elsewhere. Recovering the component monodromy itself needs separately justified continuation/alignment and global measurement coverage.

**Corollary 2 (r-1 mixed moments under flatness).** Under Theorem 2 and the experiment above, some r-1 members of the mixed grid suffice to identify the arbitrary orbit-mass vector lambda, once the marginals are known. Such a set can be selected by row-rank computation from the known orbit matrices and emission means.

**Proof.** The U_k are linearly independent because their supports are disjoint. The transform U -> V_p U V_q^T is injective. On the (r-1)-dimensional difference space {sum_k c_k U_k: sum_k c_k=0}, every pure-marginal row vanishes, because the U_k have identical marginals. Consequently the mixed rows alone have rank r-1 on this space. Select r-1 independent rows. This count concerns recovery of arbitrary mixture weights from scalar linear expectations, not just selection among finitely many connected-support candidates; the latter can need fewer tests. The required rows may be poorly conditioned.

For the S_3 example, choose the same local separating statistic for both component copies, with means p_1,p_2,p_3. The single paired moment M_11 distinguishes the diagonal and off-diagonal vertices, since

    M_11(D) - M_11(O)
      = [3 sum_i p_i^2 - (sum_i p_i)^2]/6 > 0.

It also determines their mixing coefficient. This is a concrete joint observation that removes an ambiguity no separate observations can remove.

**Proposition (sharp held-block length for fixed Bernoulli channels).** Restrict the preceding experiment to two fixed Bernoulli emission channels, with known distinct biases p_1,...,p_m and q_1,...,q_n, where m,n>=2. With arbitrary unknown couplings and prescribed strictly positive marginal masses, a total of m+n-2 readouts within a held-pair block is sufficient and worst-case necessary to distinguish all couplings. No amount of data from blocks of total length at most m+n-3 removes the worst-case ambiguity. This lower bound is for these scalar channels and arbitrary local couplings, not for richer emissions, multiple different probes, or the smaller flat-orbit family.

**Proof.** Sufficiency follows from Theorem 3 using m-1 A readouts and n-1 B readouts. For necessity, choose a nonzero vector u annihilated by the (m-1)-by-m Vandermonde matrix of degrees 0,...,m-2, and a nonzero vector v similarly annihilated at q-degrees 0,...,n-2. Put Delta=u v^T. Both vectors have zero sum, so Delta has zero row and column sums. For a word containing a A outcomes and b B outcomes, its probability conditional on (i,j) is P(p_i)Q(q_j), where the two polynomials have degrees at most a and b. If a+b<=m+n-3, either a<=m-2 or b<=n-2. Therefore the word's probability change under Delta is

    (sum_i u_i P(p_i)) (sum_j v_j Q(q_j)) = 0.

Start with the strictly positive product coupling W_0 of the prescribed marginals. Since Delta is nonzero and has zero sums, it has positive and negative entries. Set t_*=min_(Delta_ij<0) W_0,ij/(-Delta_ij). Then W_1=W_0+t_*Delta is a distinct nonnegative coupling with the same marginals, at least one zero entry, and the same probabilities for every allowed short word. Thus even full versus sparse local support is indistinguishable by those experiments. Both couplings can also be chosen in the interior by taking 0<t<t_* if only weight nonidentifiability is needed.

The sparse boundary support in this proof need not be invariant under a specified nontrivial monodromy action. It therefore does **not** establish a matching lower bound for joint-cover topology under Theorem 1 or for orbit masses under Theorem 2.

### Compatibility with nontrivial monodromy

Distinct globally continuous real biases p_i(b) can be sorted, producing global sheet labels and trivial monodromy. Therefore the scalar-statistic construction is pointwise/local. Nontrivial observable covers require multidimensional component laws, or different separating scalar statistics on different charts, with their overlap identifications supplied or recovered by an explicitly justified procedure. Finite charts, conditioning bounds, and continuation coverage must be charged when needed.

## 5. A finite-sample statement, conditional on calibrated emissions

**Proposition (known-means error and support recovery).** Suppose p_i,q_j are known exactly. Let A=V_p^(-1), C=V_q^(-1), and

    K = (max_i sum_a |A_ia|) (max_j sum_b |C_jb|).

From N independent held-pair trials, form empirical means of the bounded prefix products and W_hat=A M_hat C^T. For 0<delta<1, with probability at least 1-delta,

    max_(i,j) |W_hat_ij-W_ij|
      <= K sqrt(log(2mn/delta)/(2N)).

If every positive w_ij is at least omega>0 and the right-hand side is strictly smaller than omega/2, thresholding W_hat at omega/2 recovers support exactly on that event. A sufficient condition is

    N > (2 K^2 / omega^2) log(2mn/delta).

**Proof.** Each prefix product lies in [0,1]. Hoeffding's inequality and a union bound over mn moments give a simultaneous moment error bound eta=sqrt(log(2mn/delta)/(2N)). Entrywise multiplication yields |(A (M_hat-M) C^T)_ij| <= eta (sum_a |A_ia|)(sum_b |C_jb|). The threshold conclusion follows.

This is not an end-to-end sample-complexity theorem. Estimated emission means add calibration and matrix-perturbation error. Near-colliding means make K large. No uniform support recovery is possible without a positive-mass margin: zero and arbitrarily small positive weights induce arbitrarily close observable distributions. An independence or dependence justification is needed for the trials. Finite data do not certify exact zeros without such model assumptions; confidence sets are appropriate otherwise. Recovering topology from finitely sampled parameter locations also needs quantitative regularity and coverage, not just pointwise moment inversion.

## 6. Relation to the 28 October local-mechanism result

Comparison source: `local_mechanism_delivery/Local mechanism discovery results.txt`, read in full for this note.

That work already assumes aligned multiview and patch-history access, calibrates unknown patch alphabets and emissions, and statistically inverts bounded joint latent-state laws. It then discovers factors and dynamics using conditional independent innovations, positivity, temporal distinguishability, and a full-product support promise. Its positive local-to-global argument identifies the complete transition within a specified patch-supported log-linear class, and it separately treats failures of autonomous joint lossy summaries.

The present Vandermonde inversion is a small explicit instance of the earlier joint-law inversion step, not a stronger general discovery theorem. The cover result is complementary and narrower: it classifies what is left undetermined when the observation contract is weakened to separate component laws, and isolates conditions forcing the observable support despite that weaker access. It permits correlated joint latent weights but does not model temporal update mechanisms, so it is not a generalization to correlated innovations. It neither discovers physical wiring nor solves the earlier interface/filtering and execution-access gaps.

The useful restricted addition is the separation of three questions:

1. Which reduced joint support covers are compatible with already known component covers?
2. Which probability couplings on those supports are compatible with marginal data and any flatness restriction?
3. Which explicitly available paired experiment can distinguish them, and with what conditioning and mass margins?

Theorem 1 answers the first; Theorem 2 answers the second in a restrictive invariant setting; Theorem 3 and the proposition answer a declared version of the third. None converts marginal access into joint access by assertion.

## 7. Prior art and provenance

- The correspondence between covers and fundamental-group actions is classical. The orbit/support argument above is a direct application, not a new covering-space theorem. See [Hatcher, Algebraic Topology, Section 1.3](https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf).
- Grouped-sample mixture identification is established. [Vandermeulen and Scott, On the Identifiability of Mixture Models from Grouped Samples](https://arxiv.org/abs/1502.06644) proves identification with 2m-1 observations per held component among models with at most m components; its expanded treatment is [An Operator Theoretic Approach to Nonparametric Mixture Models](https://arxiv.org/abs/1607.00071). This is a population statement, not recovery from 2m-1 total noisy samples, and comparison with unrestricted higher-order mixtures needs the paper's stronger determinedness distinction.
- [Ritchie, Vandermeulen and Scott, NeurIPS 2020](https://proceedings.neurips.cc/paper/2020/file/866d90e0921ac7b024b47d672445a086-Paper.pdf) develops consistent estimation from grouped observations. The elementary known-means concentration bound here is not a replacement for that broader statistical theory.
- The finite Vandermonde inversion, orbit-uniform invariant measures, and rank argument are standard linear algebra. The exact combination above was checked directly, but this note does not establish that the formulation is new or exhaust the literature on joinings, couplings, or observational equivalence.
