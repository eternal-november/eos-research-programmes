# Independent mathematical review

**Document:** *Finite evidence for monodromy: rigorous lower bounds and their scope*  
**Source:** `evidence_limits.tex`  
**Reviewed SHA-256:** `a44e1e628ca0d09938035e3985b54e06a26647560c1cadc376326906ebb6b4ed`  
**Review date:** 4 November 2026

## Assessment

No remaining mathematical defects were found in the reviewed source. The claims and proofs are valid at their stated scope. This is an independent mathematical check, not a formal proof certificate or a certification of novelty.

## Claims checked

- The localized half rotation preserves positivity, separation, equal weights, and the specified complete-word Hankel Gram spectra, while changing identity monodromy to a transposition.
- The smooth unknown-modulus impossibility handles randomized adaptive querying and almost-sure finite stopping on the constant family. The alternative is one fixed family chosen after the algorithm, not a family chosen after observing its random seed. The deterministic exact-transcript statement also holds.
- The analytic statements distinguish deterministic finite exact-query impossibility from almost-sure separation of each fixed known pair by a random exact query. The noisy analytic approximation preserves the impossibility when both queried parameters and sampled symbols are almost surely finite.
- Certified nearest-neighbor transport follows from the strict inequality `omega(h) + 2 epsilon < Delta/2`. The Lipschitz and Hölder exact-query orders, packing constants, and unknown-separation stopping certificate check out.
- The regular-polygon construction cancels all nonzero Fourier modes below degree `p`, giving genuinely different monodromy with identical laws through group length `p-1`. A length-`p` word detects the rotation.
- For the rare-pair model, the two-symbol KL bound `128 w^2 Delta^4`, its adaptive stopping-time extension, and the matching known-pair testing upper bound are valid. Summing disjoint-seam KL bounds gives the stated spatial-statistical product lower bound.
- The explicit symmetric-subclass upper bound has valid constants: `m = max(2, ceil(8L/Delta))`, the Hoeffding factor `1152`, the constrained rank-one fit, and bottleneck error at most `Delta/16`.
- The common-component coupling gives the exact restart lower bound. The long-group construction correctly combines atom coverage, empirical-vector accuracy, clustering, and certified transport. Its restart and total-symbol costs are consistent.

## Assumptions and limits that matter

- The experiment is a held-mixture model: each group selects one latent component, holds the parameter fixed, and samples conditionally IID symbols. Different restarts are independent conditional on their chosen parameters.
- Atoms remain distinct and continuous. Quantitative recovery requires a supplied pathwise atom modulus and sufficiently accurate atom estimates; a moment modulus alone needs an inverse stability bound.
- The exact-query lower bound already holds with two atoms on three symbols. It is not a lower bound for scalar Bernoulli atoms, which can be globally sorted.
- The stopped-KL argument uses finite expected restart count under the null; if that expectation is infinite, the lower bound is automatic. Positive response probabilities and bounded per-observation log likelihood ratios justify the finite-expectation calculation.
- The sharp `w^-2 Delta^-4` statistical rate concerns the specified genuine monodromy pair using two-symbol restarts. The explicit broader upper bound assumes the entire symmetric subclass and known `c`, `w`, and `Delta`.
- The spatial-statistical lower and upper bounds leave a `log m` gap. The unrestricted monodromy horizon is bounded below by `p` and sufficiently above by `2p-1`; the document does not close that gap.
- The restart asymptotic `Omega(w^-1 log(1/delta))` is uniform for `delta <= 1/4`, or interpreted separately for each fixed `delta < 1/2`. The exact expression remains the operative bound.
- Exact-law queries, fixed-length restarts, arbitrarily long groups, and one nonergodic trajectory are different resources. None of these results makes finite measured tables a certificate that the assumed model class holds at unobserved horizons.

## Corrections incorporated during review

The final source explicitly restricts the exact-query lower-bound construction to a three-symbol alphabet and states the confidence regime for the restart asymptotic. The added symmetric-subclass upper bound was checked separately after its insertion.

## Reference checks

The cited [grouped-mixture identification result](https://arxiv.org/abs/1502.06644) supports the `2p-1` sufficient horizon and is correctly distinguished from a monodromy lower bound. [Kaufmann, Cappe, and Garivier, Lemma 1 and Appendix A](https://www.jmlr.org/papers/volume17/kaufman16a/kaufman16a.pdf) support the cited adaptive change-of-measure principle; the document supplies its own calculation for the present experiments.
