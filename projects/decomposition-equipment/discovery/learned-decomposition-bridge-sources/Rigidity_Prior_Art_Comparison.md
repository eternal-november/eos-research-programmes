# Prior-art comparison: residual transport rigidity

Research date: 28 October 2026. Scope: the scalar distinct-signature refinement, affine equal-signature-block refinement, and nonlinear influenced-block refinement in `Residual_Transport_Rigidity.md`; not a comprehensive priority opinion.

## Main finding

**The scalar fibre rigidity mechanism has explicit causal-representation-learning prior art, not merely a distant connection to optimal transport.** The closest exact lemma is **Brehmer–de Haan–Lippe–Cohen (2022), supplementary Lemma 2**. The closest later application is **Liang et al. (2023), Causal Component Analysis, proof of Theorem 4.2(ii)**. **Xi–Bloem-Reddy (2023), Proposition 5.2**, already states the corresponding triangular nonlinear-ICA componentwise-identification corollary. All three should be credited, rather than only generic transport uniqueness.

**I did not find the precise “distinct residual graph signatures suffice” corollary stated in S22 or S26, or in the additional results inspected here.** That is a bounded search result, not evidence of novelty. The defensible description is a *source-specific sharpening of the displayed graphical sufficient condition, obtained by combining existing consistency results with established transport rigidity*. It is not a new scalar transport theorem, and “stronger than the source's displayed criterion” must not become “stronger than every result of those authors or the literature.”

## 1. Closest explicit antecedent: scalar fibres

Brehmer et al., *Weakly supervised causal representation learning*, supplementary §A.2, **Lemma 2**, treats a differentiable family of real-valued maps carrying a fixed source measure to a fixed target measure and concludes that the map is constant in the other arguments. Its proof conjugates by CDFs and uses the two scalar orientations. The following paragraph explicitly interprets this in terms of independence of the source and output from the base. Supplementary §A.3 also discusses failure outside real-valued variables, including a circle-valued counterexample. [Published NeurIPS supplement, pp. 4–5 and 10](https://papers.nips.cc/paper_files/paper/2022/file/fa567e2b2c870f8f09a87b6e73370869-Supplemental-Conference.pdf).

For the candidate, cite the antecedent but retain the candidate's explicit global-diffeomorphism, full-support, and connected-base hypotheses and proof. Do not import the earlier lemma's compressed “differentiable measures” wording as a replacement for checking those hypotheses. The candidate also handles atoms and density zeros using a direct CDF argument; those extensions should be distinguished from the original CDF-diffeomorphism presentation.

Liang et al., *Causal Component Analysis*, **Lemma B.1** reproduces Brehmer's lemma with attribution; **Lemma B.2** states the two full-support scalar CDF transports. **Lemma B.4** establishes marginal transport for a triangular diffeomorphism. The proof of **Theorem 4.2(ii)**, pp. 19–21, combines triangularity, marginal cancellation, and B.1 to remove off-diagonal dependence under perfect interventions. **Corollary 4.8**, based on Theorem 4.5 and Assumption 4.4, gives intervention-target block identification for independent latent coordinates using full-rank score differences. Its setting has known targets, coverage of all coordinates, and repeated interventions on strict target subsets. It is a close comparator for the influenced-block argument, but is not the S26 unknown-target/temporal residual-preorder corollary. [Published NeurIPS 2023 paper](https://proceedings.neurips.cc/paper_files/paper/2023/file/67089958e98b243d5cc1881ad60418b8-Paper-Conference.pdf).

Spantini–Bigoni–Marzouk, *Inference via Low-Dimensional Couplings*, §3, supplies monotone triangular transport uniqueness. **Theorem 3 (Sparsity of Knothe–Rosenblatt rearrangements)** specializes, with an empty target independence graph and product reference, to componentwise transport. After constant orientation flips, this is another direct route to the scalar triangular-product statement under its density assumptions. This is a named general transport result, not a published mechanism-sparsity graphical criterion. [JMLR 2018 paper, §3 and Theorem 3, p. 11](https://www.jmlr.org/papers/volume19/17-747/17-747.pdf).

### Closest named triangular nonlinear-ICA corollary

**Xi and Bloem-Reddy, *Indeterminacy in Generative Models: Characterization and Strong Identifiability* (AISTATS 2023), Proposition 5.2**, states componentwise identification for triangular monotone-increasing (TMI) generators with full-support independent latent distributions. **Appendix E.1** explicitly proves that KR transports between product measures are diagonal. **Theorem 5.1** treats a fixed prior and strong identification; it is not the right result when marginal priors may change. **Theorem 2.2** characterizes indeterminacies by intersecting generator-compatible maps with prior-compatible transports. [Primary v5, §5.1 and Appendix E.1](https://arxiv.org/html/2206.00801v5#S5.SS1).

**Our application:** the source consistency result constrains the *residual* map, not the emission maps, to a triangular class after ordering singleton SCCs. Constant coordinate orientation flips make that residual map TMI; product initialization then puts it in the diagonal-product-transport case of Proposition 5.2's proof. Continuity and full support upgrade almost-everywhere equality. This is a direct reuse of an established corollary/proof, not a new triangular ICA result. The exact graph-signature inference is still a separate combination, not stated in the inspected proposition.

## 2. Exact source comparison

### S26: published support envelope versus actual equivalences

S26 **PDF Proposition 7**, §3.7, is the closest displayed complete-identification result. It assumes the graphical criterion, **Assumption 5**. The support machinery is PDF Propositions 3–5 and the consistency results (PDF Theorems 1–3; HTML Theorems 22, 24, 32). Product initialization is explicit in Assumption 2; Proposition 2 supplies diffeomorphism equivalence. §4's quasi-linear result is PDF Theorem 5 / HTML Theorem 56. HTML numbering differs from PDF numbering; prefer named results and section links. [Version-pinned source](https://arxiv.org/html/2401.04890v2), [PDF](https://arxiv.org/pdf/2401.04890v2).

**Our comparison, not a quotation:** for signature S_i = (action parents, temporal parents, temporal children), the residual support is i ≼ j iff S_i is componentwise included in S_j. Assumption 5 requires every upper set to be {i}; singleton SCCs require only pairwise unequal signatures. Thus strict comparisons are permitted by the candidate but not by the displayed criterion. The upgrade needs actual product-law transport, not graph preservation alone. An allowed shear is not an equivalent independent model.

### S22: nearest exact theorem and proof location

S22 **Theorem 5** states permutation/scaling identification under its graphical criterion and scalar invertible sufficient statistics. **Lemma 19**, Appendix A.3.1, pp. 31–33, separates variability, sparsity, and graphical steps. Equations (109)–(110), followed by matched-permutation graph equality, supply the support restriction before its final graphical step. Theorem 4 gives the constant affine relation between sufficient-statistic vectors. The initial conditional law is included in equation (1) and the full-trajectory equivalence proof. [Published CLeaR 2022 paper](https://proceedings.mlr.press/v177/lachapelle22a/lachapelle22a.pdf).

**Our deduction:** align the matched permutation; the affine map is block triangular on equal-signature classes. At fixed auxiliary initialization, its source and target statistic blocks are independent. Conditional output laws differ only by translations. A finite probability measure has no nonzero translation period, and affine nondegeneracy kills the off-block coefficients. Thus equal-signature blocks suffice. This does not follow from the conclusion of Theorem 5 after simply deleting an assumption: it uses the intermediate support proof plus an additional independence argument. Nor is generic non-Gaussian ICA the right attribution, since Gaussian blocks are allowed. No exact named moment-free affine-block lemma was located in this search.

## 3. Nonlinear blocks: what is and is not already covered

The candidate's common-stabilizer formulation is an elementary transport-coset identity: relative to one fibre transport, every other fibre differs by an automorphism preserving all block laws. Its substantive source-specific work is verifying that S26 Assumptions 6–8 yield dense local likelihood-ratio rank for precisely the acted-on or temporally influenced SCCs, with correct map orientation and density-zero/context quantifiers.

CauCA's block discrepancy result is a particularly close score-difference antecedent (above). It does not by itself verify those S26 projections or initialization/history obligations. Likewise, full rank of likelihood-ratio gradients kills connected symmetry families; it does not automatically kill disconnected symmetries, identify within-block coordinates, or make parentless multidimensional blocks rigid.

Ahuja–Hartford–Bengio's *Properties from Mechanisms* develops identifiability through shared mechanism equivariances, including stochastic mechanisms. It is useful conceptual credit for the symmetry perspective, but its mechanism-level equivalence is not identical to a fixed-context common-measure stabilizer, and it does not supply the proposed signature test. [Primary preprint, §§2–3](https://arxiv.org/pdf/2110.15796).

Zheng–Ng–Zhang **Theorem 1** concerns sparsity of the observation mixing Jacobian and a singleton intersection condition. It is not the same assumption as distinct residual mechanism signatures; citing its identifiability conclusion alone does not establish implication for this candidate. [Primary version v5, Theorem 1](https://arxiv.org/html/2206.07751v5).

## 4. Recommended claim and attribution

> Combining mechanism-sparsity consistency with classical triangular-product transport rigidity yields a distinct-signature sufficient condition in the stated full-support scalar setting. The scalar fibre rigidity step already appears explicitly in Brehmer et al. (2022), Lemma 2, and is used in CauCA's identifiability proofs; the triangular nonlinear-ICA corollary is explicitly Xi–Bloem-Reddy (2023), Proposition 5.2. We additionally give an affine block argument and a source-specific likelihood-ratio analysis of influenced residual blocks. We have not established priority for these exact corollaries.

The local proof and growing family remain useful even if every ingredient is standard. Their value is a checked implication and a strict comparison with one displayed sufficient criterion, not a priority claim or a new physical-decomposition theorem.

## 5. Search limits and reproducibility

Inspected: locally retained full S22 text (Theorem 4/5, Lemma 19 and surrounding proof); S26 v2 HTML and retained PDF text (§§2–4, §7, relevant appendices and terminology searches); primary CauCA statements and proofs cited above; Brehmer's published supplement; Spantini's transport theorem; Xi–Bloem-Reddy v5 Proposition 5.2 and Appendix E.1; Zheng's Theorem 1; Ahuja's primary preprint introduction and mechanism framework. Targeted searches included combinations of “mechanism sparsity”, “triangular”, “Knothe”, “Rosenblatt”, “distinct signatures”, “distinct parent sets”, “block diagonal”, “common symmetry”, and “likelihood ratios”.

This was not an exhaustive citation-graph review, a review of every theorem in all nonlinear ICA literature, an author consultation, or a review of unpublished work. CITRIS/ICITRIS distinct intervention-pattern results and later causal-abstraction literature appeared in search but were not fully theorem-audited here. They remain relevant before any scientific-priority claim. The exact affine-block result was not located; that negative result has especially low evidential value because its elementary form may occur under different terminology.

Access notes: an OpenReview workshop PDF URL returned a browser-verification page; the published NeurIPS supplement was independently accessible and used instead. A local download helper failed before networking because Python `requests` was unavailable; no permissions denial occurred, and primary web retrieval supplied the needed text. No external writes or author contact were performed.
