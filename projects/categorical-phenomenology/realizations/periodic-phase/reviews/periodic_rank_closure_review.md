# Independent review: periodic independent emissions, arbitrary initial phase

## Result

Stationarity is unnecessary for the periodic-independent-emission extension. A clean wholly observable hypothesis is: continuous normalized word laws on a compact Hausdorff parameter base; invariance under every finite permutation of positions that preserves their residue modulo a fixed positive integer q; and constant finite ordinary (one-symbol) Hankel rank p. These assumptions determine a p-sheeted cover of all observationally distinct phases, its rotation automorphism, emissions, initial weights, predictive bundle, and positive cone. The initial weights may vanish. The minimum continuous arbitrary-native stochastic width is still the least k admitting an equivariant map from the phase-frame cover to D_{p,k}; normalized signed width is g(E_0)+1.

The proof below does not assume any supplied latent cover, a stationary competitor, minimal competitor, or retained-state interface. It is stronger than a stationary-block theorem but uses the explicit residue-permutation symmetry. An equivalent formulation is aligned q-block exchangeability plus the observable condition that its recovered de Finetti atoms are product distributions. Merely assuming block exchangeability without product atoms is not the hypothesis of this nonstationary extension.

## 1. Observable representation

Put B=Y^q and K=Delta(Y)^q. Residue exchangeability means that the q infinite subsequences at residues 0,...,q-1 are jointly invariant under independently chosen finite permutations. The multi-class de Finetti representation gives a unique probability measure mu_x on K such that

p_x(y_0...y_{n-1}) = integral product_{t=0}^{n-1} theta_{t mod q}(y_t) d mu_x(theta).

This can alternatively be proved by the empirical-frequency compactness argument of the original draft, sampling without replacement independently within each residue class. Uniqueness follows because all mixed coordinate monomials are recovered from cylinder probabilities: to realize any such monomial, choose a long enough cylinder and sum over the unused coordinates. Polynomial density on K finishes the argument. The same moment argument gives weak continuity in x.

The product-block map b(theta)=theta_0 tensor ... tensor theta_{q-1} is injective, because its marginals recover theta. The aligned q-block Hankel is the moment Gram matrix of b_*mu. Its rank is therefore the number r_x of atoms of mu_x, by exactly the finite-support Gram argument in the original draft. In particular r_x <= p, although r_x need not be constant.

For theta in K define its infinite periodic-product cylinder function f_theta. Let R(theta_0,...,theta_{q-1})=(theta_1,...,theta_{q-1},theta_0), and define

C_x = union_{j=0}^{q-1} R^j supp(mu_x).

Repeated rotations that yield the same tuple are one phase, not several hidden states.

## 2. Rank equals the number of distinct phases in C_x

Let E_x be the ordinary predictive row space spanned by p_x(u dot). The following argument is pointwise and does not yet assume constant cardinality of the initial support.

First, for any initial atom theta_a of positive mass w_a, classify it using empirical frequencies in long aligned blocks of length qn. For any finite collection of distinct tuples, such classifiers converge in conditional expectation to Kronecker deltas. Since aligned blocks return every tuple to its starting phase,

sum_{u in Y^(qn)} phi_a(u) p_x(u dot) -> w_a f_{theta_a}

pointwise on all continuation words. E_x is finite dimensional, hence closed in the pointwise topology of R^(Y*): choose finitely many evaluation coordinates that inject E_x, and recover basis coefficients from those evaluations. Thus every original f_{theta_a} belongs to E_x.

Second, E_x is invariant under every one-symbol shift A_y f(v)=f(yv), and

A_y f_theta = theta_0(y) f_{R theta}; consequently sum_y A_y f_theta=f_{R theta}.

Thus f_c belongs to E_x for every c in C_x.

Third, these functions are linearly independent. Their q-block laws b(c) are distinct. Long-block empirical classifiers have expectations converging to the identity matrix on this finite list, so a vanishing linear combination forces every coefficient to vanish.

Finally, each reachable continuation p_x(u dot) is explicitly a linear combination of f_{R^|u| theta_a}; hence E_x is contained in their span. Therefore

rank H_x = dim E_x = |C_x|.

This is the crucial distinction between aligned block rank and native one-symbol rank.

## 3. Recover the continuous full-phase cover by stationarization

Define an entirely observable finite shift average

bar p_x(v) = (1/q) sum_{j=0}^{q-1} sum_{u in Y^j} p_x(uv).

The original law is invariant under a q-step shift, so bar p is stationary. Its directing measure is

bar mu_x=(1/q) sum_{j=0}^{q-1} R_*^j mu_x.

Its support is exactly C_x, with p distinct atoms and strictly positive masses. The original draft's local bump-function argument now applies to bar mu: C -> X is a continuous p-sheeted cover, and the bar weights are continuous and uniformly bounded below on the compact frame cover. Rotation R restricts to a continuous cover automorphism sigma:C->C satisfying sigma^q=id. Its cycle lengths may be proper divisors of q. The permutation's conjugacy class is locally constant, so it is constant on any connected base component.

Original initial weights w_c=mu_x({c}) are recovered continuously in local labels by integrating the same isolating bumps against mu_x. They are nonnegative, sum to one, and may vanish. They need not be sigma-invariant. The stationary weights bar w are sigma-invariant.

The phase functions form the canonical local frame of E; its centered subbundle is the kernel of evaluation at the empty word. Its nonnegative consistent cone is the simplicial cone generated by these p phase functions. Tests identify its rays. The reachable cone closure contains the original positive-weight rays and is closed under positive shifts; hence it contains all phase rays even when the original initial weight on a phase is zero.

## 4. Arbitrary-native necessity at the same width

Suppose any continuous native realization has initial row rho and outcome kernels N_y, with T=sum_y N_y stochastic. No stationarity or minimality is required. Then

bar rho=(1/q) sum_{j=0}^{q-1} rho T^j

is a continuous probability row and (bar rho,N_y) realizes bar p at exactly the same width k. Although bar p is stationary, bar rho need not be stationary as a hidden distribution; no such assertion is needed.

Use classifiers on two adjacent length qn blocks. Conditional on a phase of bar p the blocks are independent and identically distributed, since sigma^(qn)=id. The matrices R,Q,L and the threshold repair in the original exchangeable proof therefore work unchanged, with bar weights and tuple classifiers. They extract an equivariant exact stochastic split Q'L'=I_p from the arbitrary native competitor at the original width k.

For explicit constants, let delta be the minimum sup-norm separation of distinct q-tuples on the compact frame cover. Each residue contributes n iid emissions. A union bound over q|Y| coordinates gives epsilon_n=2q|Y| exp(-n delta^2/32). Taking n >= ceil((32/delta^2) log(16q|Y|/bar w_*)) gives epsilon_n <= bar w_*/8. The original thresholds 3/4 and 2/3 and the 6/7 diagonal bound apply exactly.

## 5. Sufficiency and native kernels

In local phase coordinates let S_{ab}=1 when b=sigma(a), and D_y=diag(theta_a,0(y)). Then the canonical outcome matrix is A_y=D_y S. It satisfies A_w 1=f_a(w) rowwise. Let (Q,L) be any continuous equivariant stochastic split, QL=I_p. Define

rho=wQ, N_y=L D_y S Q.

These descend independently of local labels, are nonnegative, and sum to the stochastic matrix T=L S Q. Telescoping QL proves all-word equality. Thus the same D_{p,k} criterion applies, and width depends only on the underlying phase cover, not on sigma or the initial weights, within this observable class.

The ordinary state-emitting requirement also costs no extra states. For emission-then-transition choose e_y=L d_y, where d_y=(theta_a,0(y))_a, and use diag(e_y)T. The identity Q diag(e_y)=D_y Q yields the correct laws. For transition-then-emission, replace d_y by its inverse-phase shift tilde d_y(b)=d_y(sigma^{-1}b); then S diag(tilde d_y)=D_y S, so T diag(L tilde d_y) gives the same laws. The two emission conventions require different emission vectors in general.

For normalized signed necessity, stationarize the signed initial row exactly the same way and repeat the original finite-block full-rank embedding argument with positive target bar weights. Sufficiency uses the centered-bundle split and the same L D_y S Q formula. Hence signed width remains g(E_0)+1.

## 6. Uniform finite-horizon obstruction

If an arbitrary continuous stochastic competitor approximates the original law to TV error at most beta at horizon H=2qn+q-1, then every tail window of length 2qn at offsets 0,...,q-1 also has error at most beta, by marginalization. Averaging these windows gives a bar-law competitor at error at most beta. Thus beta=bar w_*/64 and the original threshold argument give the exact cover obstruction. This adds at most q-1 symbols beyond the stationary two-block horizon. If the target itself is stationary, H=2qn suffices without stationarization.

## 7. Precise warning examples

### Aligned block rank does not count native phases

Take q=2, Y={0,1}, and a single periodic product tuple (Bernoulli(1/3), Bernoulli(2/3)), starting in that fixed phase. The aligned block law is IID, so its block Hankel rank is 1. The ordinary predictive space contains its two rotated periodic-product functions, which are distinct and independent, so ordinary Hankel rank and native stochastic width are 2. Thus applying the old criterion to initial block atoms alone gives the wrong answer even over a point. Stationarization recovers both phases.

### Non-product block atoms are outside the nonstationary theorem

Let blocks be IID (B_n,B_n), with B_n a fair bit. The aligned block Hankel rank is 1, but the block atom Q(00)=Q(11)=1/2 is not product. This process is not residue-exchangeable: within-residue permutations break pair equality. It cannot be treated as one independent-emission phase. It has a three-state native presentation (a boundary state chooses and emits a fair bit, then a state remembering that bit repeats it and returns to the boundary), and its predictive row space has dimension 3. Thus block exchangeability alone permits within-block memory. In the stationary setting, one-symbol strict stationarity together with aligned block exchangeability does force product atoms. The complete empirical-limit proof is included in `observable_research/stationary_block_exchangeability_audit.tex` and in the main manuscript: the block directing measure is invariant under F(q)=q_suffix tensor q_first, while F^q maps every block law to the product of its marginals. This sharpening needs no finite-rank assumption.

## 8. Genuine nonexchangeable Moore-space separation

Use the original Moore base X=M(Z/3,1), its regular three-sheeted C3-cover, and the original strictly positive affinely independent emissions v_a on four symbols, built from the nontrivial centered oriented plane bundle E_0 with trivial E_0 plus R. The cover has a global cyclic automorphism sigma. Set theta_a=(v_a,v_sigma(a),v_sigma^2(a)) and initial weights 1/3.

The law p(y_1...y_n)=(1/3) sum_a product_t v_sigma^(t-1)(a)(y_t) is stationary and residue-exchangeable modulo 3, with three distinct phases. Its predictive bundle is the same R plus E_0, and the exact widths are: pointwise 3, continuous normalized signed 4, continuous stochastic 5. The old free-group obstruction on D_{3,4}/S_3=K_4 and the D_{3,5} upper bound carry over without changes.

It is nonexchangeable already at length two. If V is the 3-by-4 matrix of emission rows and S the three-cycle matrix, its two-output joint table is J=(1/3)V^T S V. Affine independence and unit row sums imply rank V=3. If J were symmetric, then V^T(S-S^T)V=0; multiplication by a right inverse of V on both sides would give S=S^T, false. Thus some p(yz) differs from p(zy) at every parameter value. This is genuine temporal order, not merely a hidden periodic label imposed on exchangeable laws.

## 9. Primary-source audit

Carl Graham, “Convergence of multi-class systems of fixed possibly infinite sizes,” arXiv:0902.0539 (2009), Theorem 3, directly supplies conditional independence of the residue classes given their directing-measure vector. Its discussion identifies the all-infinite case with Aldous (1985), Corollary 3.9, p.25. This supports the representation ingredient, not the topological width criterion. Primary PDF inspected: https://arxiv.org/pdf/0902.0539 .

Finesso and Prosdocimi, “Partially Exchangeable Hidden Markov Models,” ECC 2009, and Prosdocimi and Finesso, “Countable Partially Exchangeable Mixtures,” arXiv:1306.5631 / Journal of Theoretical Probability 29 (2016), concern Markov exchangeability based on transition counts and countable mixtures of Markov chains. That is a different symmetry from independent permutations within fixed residue classes; cite as neighboring realization work, not as the precise representation theorem here. Primary author preprint: https://arxiv.org/abs/1306.5631 .

Bru, Cantó and Ricarte, “On realizations of periodic compartmental systems,” MTNS 2004, situates periodic positive-system realization within classical convex-cone realization theory. Its periodic linear systems are not the continuous parameter-family/observable phase-cover statement proved here. Primary conference text: https://mathweb.ucsd.edu/~helton/MTNSHISTORY/CONTENTS/2004LEUVEN/CDROM/papers/49.pdf .

No novelty claim follows from this limited audit. The candidate family-level contribution remains the same-width extraction from arbitrary native competitors and the exact cover-section criterion; the periodic extension adds observable rotation closure and, in the nonstationary formulation, finite shift averaging.


## 10. Frozen-manuscript verification

Reviewed `observable_research/periodic_phase_observable_theorem.tex` at SHA-256 `1098741a19d81f52f1371eed6b0a391b9f65e3302f7ba11e0409452b5af1eab3` on 4 November 2026. The source hash was checked directly.

The review covered observable reconstruction, finite-dimensional pointwise closure, the full rotation cover and initial-weight continuity, arbitrary-native necessity and its exact stochastic repair, both ordinary HMM conventions, normalized signed width, the finite-CW and compact-Hausdorff existence bounds, the quantitative horizon H=2mt+m−1, the stationary-block sharpening, and the nonexchangeable Moore-space example. No mathematical blocker was found in these arguments.

In particular, transition-then-emission correctly uses the shifted emission matrix Pi^{-1}D_y Pi; it does not reuse the unshifted emission vector. The nonstationary approximation theorem correctly allows the additional m−1 prefix symbols needed for observable shift averaging. The initial block rank is not substituted for the full ordinary rank.

This is an independent proof review of the specified source version, not a priority certification or an assertion that the cited classical ingredients are new.
