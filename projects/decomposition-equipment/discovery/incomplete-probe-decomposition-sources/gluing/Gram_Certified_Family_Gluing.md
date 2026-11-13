# Family-preserving gluing from response equalities, without latent identification

This is a proposed integration lemma for the main discovery result. It is not a stand-alone claim that arbitrary readouts provide the necessary Gram matrix.

## Hypotheses

There are finitely many context-labeled response coordinates f_j(z) in [0,1]. A positive reference distribution m on finite hidden modes gives a measured matrix
G_jk = E_m[f_j(Z) f_k(Z)].
The same m must apply to the compared contexts. If different context settings produce different hidden laws, equality of a cross-context Gram matrix is not justified. Two independently noisy response trials conditional on the same Z suffice to measure each entry; squaring one Bernoulli observation does not. Known channel corrections can be incorporated only with their own calibration proof.

Let Ω(G) contain all positive latent realizations (Z,m,{f_j},source dynamics,etc.) consistent with G and the remaining evidence. Hidden cardinality and labels need not be common across worlds. Ω(G) is NOT replaced by independent choices of f_j or independent source choices across time.

## Theorem A: realization-uniform response equations

For a real coefficient vector v,
v^T G v=0
if and only if sum_j v_j f_j(z)=0 for every positive-support hidden mode in EVERY realization in Ω(G), assuming Ω(G) is nonempty.

Proof: in each realization v^T G v=E_m[(sum v_j f_j)^2]. Positivity proves pointwise zero. Conversely any realization satisfying pointwise zero gives the same measured zero value. Thus a Gram nullspace certifies equations, even when it does not identify any f_j, Z, m, or source transition.

This is the key distinction from reconstructing the whole response algebra or a full mixture decomposition: only the equations required for the quotient are identified. Higher joint moments, source dynamics, and even effective atom locations may remain ambiguous.

## Theorem B: quotient refinement and gluing

Suppose a primitive component has finite old state x, admitted input u, and next state y. The coordinate list includes f_(x,u,y)(z)=P(y|x,u,z). For a next-state block B, the block response is sum_(y in B) f_(x,u,y). Consequently equality of block response rows for x,x' is exactly a Gram-nullspace test with coefficients +1 for (x,u,y), -1 for (x',u,y), y in B.

Start with the task partition Π0. Split each current block according to all these row-equivalence tests over admitted inputs and current target blocks. The resulting terminal partition Π* is the coarsest refinement of Π0 that is strongly lumpable POINTWISE IN z, and it is the same partition in every realization in Ω(G).

Proof: each split tests the ordinary strong-lumpability equality, simultaneously in every world by Theorem A. Any pointwise-lumpable refinement of Π0 refines every iteration, by induction: its target blocks refine the current ones, and summing its equal response rows proves every current test. Termination is finite. At termination all defining equalities hold. This is standard partition refinement supplied with a new source of exact equality certificates, not a new partition-refinement mechanism.

Now suppose several primitive components have fresh updates conditionally independent given the SAME source mode and old contexts. For each world choose representative rows of Π*_i to define quotient local kernels. Their product is independent of the chosen old representatives, since each individual block response is pointwise equal. Therefore these component quotients assemble to an exact positive one-step quotient of the original joint output kernel in EVERY world, although the resulting averaged joint kernel can differ across worlds.

It is important that this is one shared world. Substituting quotient kernels from different members of Ω(G) has no justification. The Gram equations certify representative-independence inside each world, not rectangular freedom across worlds.

If some output coordinates overlap, do not multiply their marginal kernels. Retain a common primitive output record, apply the joint summary map to that record, and test any additional necessary joint block responses. Conditional independence of primitives may allow factorization of the required probabilities; independence of overlapping summaries does not follow.

## Dynamic qualification

To promote the preceding one-step statement to an exact Markov quotient on (quotient local states, source state), the source's own transition and all feedback interfaces must also descend through the retained quotient state. Otherwise retain the discarded fiber in the source/remainder process and state explicitly that this is an inward response quotient, not a closed Markov subsystem.

When that dynamic condition holds, equality of finite path laws follows by induction using the common initial pushforward and one-step quotient kernel. All refinement orders commute because the same maps are applied to one record. New evidence restricts Ω(G) worldwise and preserves all these equalities.

## Why the unresolved family can remain genuinely nontrivial

A Gram matrix fixes degree-two response moments, not all higher moments or temporal laws. For example, different positive source distributions on three fair response coordinates can have identical first/second moments and different triple moments. A fixed source process can additionally have unresolved temporal dependence consistent with the observation protocol. The quotient equations are universal across that family even though a global trace probability need not be.

Thus this lemma can support useful decomposition discovery before hidden architecture identification, PROVIDED the readout protocol genuinely supplies the response Gram comparisons and the task quotient is nontrivial. Its adequacy assumption is paired same-mode response access, not complete exterior probing. It must not be advertised as assumption-free or automatically easier to build physically.
