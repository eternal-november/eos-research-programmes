# Source-credit addendum: finite-field frame checking and blind dynamics

28 October 2026. Concise primary-source audit requested after the bounded-moment proposal checker was formulated.

## Exact population frame checker is classical

**Arie Yeredor, *Independent Component Analysis Over Galois Fields*, arXiv:1007.2071, Theorem 2 (PDF p.11), with proof in Appendix A.** Suppose s has K mutually independent, nondegenerate, nonuniform coordinates in GF(2) or GF(3). If the K nontrivial linear forms comprising y=Ds are pairwise independent, then D is a permutation matrix times an invertible diagonal matrix. Thus y is mutually independent and unmixed. Over GF(2), the diagonal ambiguity is trivial. Theorem 1 separately gives identifiability of invertible mixing up to permutation/scaling under its population assumptions. The paper explicitly distinguishes larger prime fields, where the pairwise implication fails, and restricts its sampling discussion to iid temporal sources. [Primary paper](https://arxiv.org/pdf/1007.2071).

**Consequence:** the population “pairwise moments validate the recovered binary source frame” implication must be credited to finite-field ICA. Writing binary independence as `E[(-1)^(u+v)] = E[(-1)^u] E[(-1)^v]` is its Fourier-coordinate specialization, not a new identification principle. A quantitative gap obtained from explicit source-bias bounds is an additional calculation; it should not absorb priority for the underlying nonmixing theorem.

**Gutch–Gruber–Yeredor–Theis (2012), *ICA over finite fields—Separability and algorithms*, Signal Processing 92(8), 1796–1808.** This extends the ICA model to arbitrary finite fields, gives separability conditions and three algorithms. The abstract and publication details were checked at primary publisher/institutional records; no uninspected theorem number is asserted. [Primary publisher record](https://doi.org/10.1016/j.sigpro.2011.10.003).

## Sparse parity learning is the correct algorithmic baseline

**Di Yan, Yu Yu, Hanlin Liu, Shuoyao Zhao, Jiang Zhang (2021), *An improved algorithm for learning sparse parities in the presence of noise*, Theoretical Computer Science 873, 76–86.** The paper studies recovery of a sparse binary parity under noisy examples and develops algorithmic time/sample tradeoffs using majority voting, search-to-decision reduction, Goldreich–Levin list decoding and sample amplification. This is direct baseline credit for sparse noisy parity search, not evidence that the present trajectory problem is LPN-hard. [Primary article](https://doi.org/10.1016/j.tcs.2021.04.026).

Any imported algorithmic theorem needs a matching example distribution, noise model, secret sparsity regime and access model. Current trajectory records, deconvolved bounded-support moments and action coverage are not automatically standard LSPN samples. Conversely, enumerating bounded-support parity candidates is not a novel search primitive. No LPN hardness reduction for this project has been established by this audit.

## Blind autoregressive dynamics plus ICA is established

**Nitta–Sugimoto–Satoh (2005), *Blind System Identification of Autoregressive Model Using Independent Component Analysis*, Transactions of SICE 41(5), 444–451.** Their primary abstract describes identifying a multi-input/multi-output autoregressive model without observing its inputs, using an augmented state-space expression, ICA and a natural-gradient numerical search. This establishes the conceptual “blind autoregressive identification plus ICA” baseline; it is not the same finite-field/noisy-readout theorem or finite-sample guarantee. [Primary journal article](https://www.jstage.jst.go.jp/article/sicetr1965/41/5/41_5_444/_article/-char/en).

## Correct integration claim

The present package may claim the proved composition of **its explicit** noisy-trajectory assumptions, bounded-support deconvolved moment estimates, quantitative acceptance thresholds, finite candidate validation, exact recovered recurrences and typed persistent-interface compilation. It should call finite-field ICA nonmixing, sparse-parity search, blind AR+ICA, compatible-basis sharing and coding/covering bounds established ingredients. This audit does not establish novelty of the full composition against all literature; it identifies the precise claims that cannot be credited as new.
