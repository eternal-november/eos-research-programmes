# Periodic reconstruction and realization: literature boundary

This is a targeted literature check, not an exhaustive novelty certificate. The finite-mixture identification layer is established. The most plausible additional contribution is the global, continuous, fixed-state nonnegative realization problem over a parameter space, together with a precise obstruction/classifier. That requires a separate proof and should not be conflated with pointwise identifiability.

## 1. Grouped observations already identify arbitrary finite mixtures

Robert Vandermeulen and Clayton Scott, *An Operator Theoretic Approach to Nonparametric Mixture Models*, Annals of Statistics 47(5), 2704–2733 (2019), DOI 10.1214/18-AOS1762.

- [Author manuscript](https://web.eecs.umich.edu/~cscott/pubs/aos_mixture.pdf)
- [arXiv manuscript](https://arxiv.org/pdf/1607.00071)

Theorem 4.1: a mixture with p distinct components is identifiable from 2p−1 conditionally iid observations against mixtures with at most p components. Theorem 4.3: 2p observations give determinedness against arbitrary finite competing mixtures. Both thresholds are sharp without further assumptions. The paper also gives spectral recovery methods.

Application here is a direct reduction: an aligned period is one observation in the enlarged alphabet A^m. Thus recovery of finite periodic-product mixture components after blocking, by itself, is not a strong novelty claim. Once a block component is recovered and is known to be a product, its phase distributions are simply its coordinate marginals. Do not claim the unrestricted 2p threshold as a new periodic bound. A stronger bound exploiting the periodic or stationary subclass would require separate analysis.

## 2. General product-mixture and HMM identifiability

Elizabeth Allman, Catherine Matias, and John Rhodes, *Identifiability of parameters in latent structure models with many observed variables*, Annals of Statistics 37(6A), 3099–3132 (2009), DOI 10.1214/09-AOS689.

- [Primary manuscript](https://arxiv.org/pdf/0809.5032)

Theorems 8–9 identify nonparametric finite product mixtures under linear-independence assumptions and at least three conditionally independent observed variables or blocks. Theorem 6 gives generic identification of an r-state HMM from 2k+1 observations when binomial(k+κ−1,κ−1)≥r, for κ observable symbols. These are pointwise identification results. Generic identifiability of the unrestricted HMM does not automatically settle a constrained deterministic-cycle subfamily, which can lie entirely in an exceptional locus. Conversely, general mixture uniqueness is already available without declaring a new HMM theorem.

## 3. Seasonal HMMs are neighboring, but not identical, prior art

Augustin Touron, *Consistency of the maximum likelihood estimator in seasonal hidden Markov models* (2018).

- [Primary manuscript and theorem](https://arxiv.org/html/1802.08161)

Section 2.2 proves identification modulo phase-dependent state relabelings under phasewise invertibility/irreducibility, an ergodic period transition product, and independent emission distributions. Parametric coefficients require an extra injectivity assumption. This does not directly cover the deterministic finite-cycle model. The printed “one-period” horizon should not be repeated without checking boundary triples; the proof and T=1 case suggest an indexing issue. Use this source to delimit broad seasonal-HMM claims, not as a theorem about the present global topological problem.

## 4. Beyond ordinary exchangeability is already a classical direction

Cecilia Prosdocimi and Lorenzo Finesso, *Countable Partially Exchangeable Mixtures*.

- [Primary manuscript](https://arxiv.org/pdf/1306.5631)

Theorem 3.2 restates Dharmadhikari's characterization: a discrete exchangeable process is a countable iid mixture exactly when it has an HMM representation with recurrent hidden chain. Theorem 3.3 extends this to partially exchangeable sequences with fixed initial state and countable Markov mixtures. The paper explicitly states finite versions when the observation alphabet is finite; it also treats Polish-valued observations.

Their partial exchangeability is expressed through successor arrays, not the fixed-length aligned-block symmetry used here. Consequently, “extension beyond exchangeability” is too broad a novelty description. The relevant distinction is the exact symmetry, family topology, and fixed ambient state-space requirement.

## 5. Nonnegative realization is not just finite Hankel rank

Alex Heller, *On Stochastic Processes Derived From Markov Chains*, Annals of Mathematical Statistics 36(4), 1286–1291 (1965), DOI 10.1214/aoms/1177700000.

- [Original DOI](https://doi.org/10.1214/aoms/1177700000)
- [Vidyasagar's detailed theorem/proof exposition](https://personal.utdallas.edu/~mxv091000/Research/hmm-full.pdf)

The exposition's Theorem 6.1 gives the stable-polyhedral-set criterion for an HMM realization. Its Theorem 7.1 gives a minimal real quasi-realization from finite Hankel rank, with minimal such realizations related by similarity. Section 5 recalls finite-Hankel-rank processes without finite nonnegative realization. Thus a proposed extension must exhibit a positive invariant structure, not merely reconstruct a vector bundle or linear operators.

The same exposition identifies Dharmadhikari's 1969 result, *A note on exchangeable processes with states of finite rank*, Annals of Mathematical Statistics 40(6), 2207–2208: exchangeability plus finite Hankel rank guarantees an HMM realization. The original 1969 article was not inspected in this pass, so its exact formulation should be checked before asserting an equivalence or sharp dimension from that citation.

## Independent deduction useful for the proposed theorem

The companion file `stationary_block_exchangeability_audit.tex` verifies a stronger reduction: one-site strict stationarity plus exchangeability of aligned m-blocks already forces the block directing measure to be supported on product distributions. The proof uses the shifted empirical-block map F(q)=q_{2:m}⊗q_1, invariance μ=F_*μ, and F^m(q)=⊗_j q_j. Finite support then yields the observable phase permutation and canonical p-state cycle realization. This proof does not establish that the fact is new.

## Recommended novelty wording

Safe provisional formulation: “We study the additional obstruction to choosing finite-state nonnegative realizations continuously over a parameter space, for an observable class admitting a periodic-product decomposition. Classical de Finetti and finite-mixture identification results provide the pointwise reconstruction layer; our proposed classification concerns global state-space stabilization.”

Before claiming novelty, compare the actual classifier and obstruction with parameter-dependent realization, continuous nonnegative factorization, and vector-bundle realization theory. A keyword search in this pass did not locate an exact match, which is evidence of search incompleteness rather than proof of absence.
