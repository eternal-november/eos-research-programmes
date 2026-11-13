# Universal product-factor rigidity and generic finite identification

This is a self-contained proof of a classical tensor-preserver specialization, not a claim of a new rigidity mechanism. A relevant general antecedent is Roy Westwick, *Transformations on tensor spaces*, Pacific Journal of Mathematics 23(3), 1967, Theorem 3.4: https://msp.org/pjm/1967/23-3/pjm-v23-n3-p21-p.pdf . The generic finite-candidate and numerical-gap consequences below are stated separately for this application.

## Exact theorem
Let `X = ∏_{i=1}^n X_i` and `Y = ∏_{j=1}^m Y_j`, with finite, nonempty index sets and finite alphabets of size at least two. Let `f:X→Y` be a bijection. The following are equivalent:

1. For every strictly positive product probability measure `p=⊗_i p_i` on X, the pushforward `f_*p` is a product probability measure on Y.
2. There is a partition of `{1,…,n}` into nonempty sets `I_1,…,I_m` and bijections `g_j:∏_{i∈I_j}X_i→Y_j` such that `f_j(x)=g_j(x_{I_j})`.

In particular, universal product-preserving recodings can merge factors and arbitrarily relabel the resulting merged alphabet, but cannot split or twist factors across outputs. No equality of the two factor shapes is assumed.

## Elementary proof
Introduce algebraically independent real variables `t_{ia}`, one for each `i` and `a∈X_i`, and write

`S_i = ∑_{a∈X_i} t_{ia}`, `Z=∏_i S_i`, and `M_x=∏_i t_{i,x_i}`.

For an output coordinate j and value b define its marginal numerator

`A_{jb}(t) = ∑_{x:f_j(x)=b} M_x`.

Each A is nonzero, has coefficients zero or one, and is homogeneous of degree one in each input-variable block i. For positive t, the normalized input law is `p_t(x)=M_x/Z`. If `y=f(x)`, independence of its output coordinates gives

`∏_{j=1}^m A_{j,y_j}(t) = M_x Z^{m−1}`.  (1)

The equality holds on an open set, hence as a polynomial identity. Fix j,b and choose any y with y_j=b (possible by surjectivity). Unique factorization in the real polynomial ring implies every irreducible factor of A_{jb} is either one of the variables t_{ia} appearing in M_x, or one of the linear polynomials S_i. These linear factors are pairwise nonassociate; the alphabet-size-at-least-two condition ensures S_i is not a variable. Since A has degree one in every block, it follows that

`A_{jb} = c · ∏_{i∈J_{jb}} t_{i,a_i} · ∏_{i∉J_{jb}} S_i`.

Its nonzero coefficients are one, so c=1. Consequently every coordinate fiber `{x:f_j(x)=b}` is a cylinder: it fixes exactly the coordinates in J_{jb} and leaves all remaining coordinates completely unrestricted.

Say input coordinate i is active for output coordinate j if some j-fiber fixes i. If it is active, then for every a∈X_i some j-fiber fixes i to a. To see this, take a fiber fixing i, choose compatible values of all other coordinates, and vary only i. The fiber containing each resulting point cannot leave i unrestricted: if it did, it would also contain the original point and overlap the original fiber. Thus it fixes i to the value chosen. (For the original value use the original fiber.)

No i can be active for two different outputs j,k. Otherwise, choose a j-fiber fixing i to a and a k-fiber fixing i to a'≠a. They are disjoint, whereas surjectivity onto the full Cartesian product Y requires every j-fiber to meet every k-fiber.

Every i is active for some j, since otherwise all output coordinates ignore it and f is not injective. Define I_j as the input coordinates active for j; these sets partition the input indices. Moreover, every j-fiber must fix every i∈I_j. Otherwise choose this fiber and any value of every other output coordinate. Their joint fiber is nonempty by surjectivity, but leaves i unrestricted because no other output is active for i; its size is therefore at least two, contradicting injectivity. Thus every j-fiber fixes precisely I_j. The fibers partition X, so they correspond bijectively to all assignments on X_{I_j}. This gives g_j and its bijectivity. I_j cannot be empty because |Y_j|≥2 and all its fibers are nonempty. The converse is immediate from independence of disjoint groups. QED.

## A single generic product law is enough (finite state set)
Fix the true finite Cartesian structure X, and regard its strictly positive product laws as parametrized by the interiors of its factor simplices. Enumerate every possible ordered factor shape `(d_1,…,d_m)`, with each d_j≥2 and ∏_j d_j=|X|, and every bijection from X to the corresponding standard product alphabet. This is a finite family. Duplicate orderings/labels are harmless.

For a candidate recoding f, output independence is characterized by the vanishing of all 2×2 minors of every one-coordinate-versus-the-rest flattening of its probability tensor. In the positive region these rank-one conditions imply a full product tensor. After substituting `p(x)=∏_i p_i(x_i)`, the minors are polynomial functions of the free simplex parameters, of degree at most 2n. If the candidate is not a coarsening in the theorem, at least one such polynomial is not identically zero on the product-simplex parameter space. Otherwise all positive product laws would satisfy independence, contradicting the theorem.

Therefore the product laws admitting any noncoarsening candidate lie in a finite union of proper algebraic subsets of the product-simplex parameter space. Its complement is relatively open, dense, and full Lebesgue measure. A single law in that complement has **exactly** the coarsening factorizations of the true factors.

It follows that its finest Cartesian factorization recovers the true coordinate alphabets/cardinalities and coordinate maps, up to permutation of factors and independent bijections of each factor alphabet. Here “finest” can mean maximal under refinement, or maximum number of nontrivial factors: all admissible factorizations are coarsenings, and the true structure is the unique finest one up to those symmetries.

This is a generic theorem, NOT a theorem for every product law. The uniform law admits every Cartesian bijection. Other algebraically exceptional laws may admit accidental decompositions. The genericity is relative to the entire unconstrained product-simplex family; a mechanism-generated lower-dimensional family can lie wholly in an exceptional set. One must establish excitation/nondegeneracy for that family rather than invoke genericity automatically.

## Several rows and quantitative separation
Suppose L exact probability rows p^(r) on the same finite atomic state set are each product in the true coordinates. For a candidate f, define

`D_f = max_{r,j,minor} |minor_j(f_*p^(r))|`.

A true coarsening has D_f=0. If every noncoarsening candidate fails independence on at least one observed row, finite enumeration gives the strictly positive instance-dependent gap

`δ = min_{f noncoarsening} D_f > 0`.

(If there are no noncoarsening candidates, identification is trivial.) One generic row suffices; multiple rows can establish separation even when no individual row rules out every bad candidate. Finite collection of separating rows exists for any generating family on which no bad candidate preserves independence identically, by picking one witness row per bad candidate.

If estimated atomic probabilities are genuine probability vectors and satisfy `max_{r,x}|p_hat^(r)(x)−p^(r)(x)|≤ε`, each 2×2 minor changes by at most 4ε: each of its two products changes by at most 2ε because entries lie in [0,1]. Permuting atoms into candidate tensors preserves the entrywise error. Therefore true-coarsening scores are ≤4ε, and every noncoarsening score is ≥δ−4ε. If ε<δ/8, a threshold strictly between 4ε and δ−4ε separates the two classes. Taking the finest surviving factorization recovers the true one.

There is no uniform positive δ over all positive product laws: laws can approach the uniform law, at which every candidate has score zero. A claimed uniform finite-sample guarantee must explicitly supply an excitation/separation lower bound (or derive a probabilistic anti-concentration bound under an assumed law of the parameters).

For K=|X|, L rows, and N independent samples per row, elementary indicator Hoeffding plus a union bound gives `max_{r,x}|p_hat^(r)(x)−p^(r)(x)|≤sqrt(log(2KL/η)/(2N))` with probability ≥1−η. Thus the separation condition is met, for example, when `N > 32 δ^(−2) log(2KL/η)`. Conditional, dependent, reconstructed, or latent rows require their own valid concentration/reconstruction bound; this iid estimate must not be transferred to temporal histories without justification.

## What this establishes for local mechanism discovery
For bounded local alphabets, brute-force candidate enumeration is finite (though factorial in the local atomic alphabet size), and the argument is independent of the nonlinearity of a mean readout. It establishes recovery of unsupplied Cartesian factors from sufficiently separated **full atomic probability rows**, once those rows and their common atom alignment have been recovered. It does not by itself recover latent atoms from means, identify a multiview emission model, establish alignment across patches, recover interfaces, or prove that the available temporal conditioning rows supply the requisite excitation. Those are separate premises/steps. In particular, conditional independence of multiview observations alone should not be conflated with the product-law structure of the latent local-coordinate rows needed here.
