# Source and priority audit

Audit date: 2026-11-05. This is a targeted primary-source comparison, not an exhaustive literature search or a proof of global priority.

## Closest exact algebraic predecessor

Stephen Zhang and Gabriel Peyré, *Global Exponential Convergence of Two-Layer Linear Network Training*, arXiv:2610.09356v1, 7 October 2026.

Source: https://arxiv.org/html/2610.09356v1

Pinpoints: Proposition 2.1; Section 3, equation (9); Appendix C.5, equation (41), Lemma C.14 and equation (42).

After adjusting width normalization and exchanging the input/output order, equation (9) is precisely the block-Gram congruence recursion used in our proof. Equation (41) is precisely the product update, including its quadratic stepsize term. Lemma C.14 evolves the transported indefinite identity and explicitly tracks its discrete conservation defect. Therefore neither covariance closure, the finite-step correction, nor the failure of exact J preservation is a new mechanism here. Their theorem concerns convergence and support margins, not an all-target two-step response-equivalence classification. I did not locate that classification in the inspected paper.

## Closest Gram-fiber and continuous-shift predecessor

Shengye Tao, *When Parameter Gradient Flows Close in Representation Space*, arXiv:2610.27474v1, 20 October 2026.

Source: https://arxiv.org/html/2610.27474v1

Pinpoints: equations (3)–(4); Appendix B.2; Section 7, “Known positive matrix flows and larger closed states”; Lemma 3.8.

The paper uses the same block Gram and indefinite matrix. Appendix B.2 derives the scalar-identity ambiguity from equality of the mobility operator. Section 7 explicitly observes that an appropriate constant multiple of J can be subtracted from a covariance without changing its continuous flow, because the control matrix anticommutes with J. Lemma 3.8 gives exact effective-width reduction via hidden orthogonal transformations. Its main quantifier is all autonomous losses from one initialization, distinct from two-initialization equivalence under changing targets. The paper expressly does not claim a discrete-time classification.

## Broader predecessors, with distinct questions

Sibylle Marcotte, Gabriel Peyré and Rémi Gribonval, *Intrinsic training dynamics of deep neural networks*, arXiv:2508.07370v2, 12 March 2026, ICLR 2026.

Source: https://arxiv.org/html/2508.07370v2

Theorems 3.8–3.9 and Proposition 3.10 concern intrinsic continuous dynamics, relaxed balance and the scalar case. This provides the relevant existing language of intrinsic mobility, rather than a new universal-property interpretation. It does not by itself settle our switched-target finite-step test.

Daniel Kunin, Javier Sagastuy-Brena, Surya Ganguli, Daniel L. K. Yamins and Hidenori Tanaka, *Neural Mechanics: Symmetry and Broken Conservation Laws in Deep Learning Dynamics*, arXiv:2012.04728v2, ICLR 2021.

Source: https://arxiv.org/html/2012.04728

Sections 4–6 and Appendix I establish the broad prior phenomenon: finite learning rates can break conservation laws of gradient flow. Consequently the broad slogan “discrete training distinguishes what the flow hides” should not be sold as an unprecedented principle. The exact observable-state classification is a different, narrower proposition.

Tianyu Pang, Vignesh Kothapalli, Shenyang Deng, Haohui Wang, Dawei Zhou and Yaoqing Yang, *Balancing Learning Rates Across Layers: Exact Two-Step Dynamics and Optimal Scaling in Linear Neural Networks*, arXiv:2606.00340v1, 29 May 2026.

Source: https://arxiv.org/html/2606.00340v1

Sections 3–5 and Appendix C analyze exact early finite-step gradients and loss for linear networks, emphasizing layer-wise learning rates and initialization. Thus merely deriving a two-step formula is not novel. The inspected statements concern learning-rate selection, not equivalence classes under all target pairs.

## Exact defensible conclusion

The two-step iff statement, its nonscalar/scalar distinction, and its fixed-target counterexample are verified mathematical consequences. I did not locate their exact combination stated in this targeted search. That absence is weak evidence, not certification of originality. Their proof follows by a short substitution into published covariance and defect identities, combined with the elementary kernel of a Kronecker-sum operator. The proper current classification is a concise independently verified corollary/refinement candidate of existing theory. It is not established as a substantive new theorem or a new conceptual framework. Practical importance remains separate and unestablished.

The sharp quantifier is all changing target pairs, with full-matrix residual control and matrix observation. “Every fixed squared loss” is insufficient: the diagonal shifted pair is indistinguishable for all time under each constant target. Two-step sharpness is only needed when the allowed widths admit a nonzero shift; for a common fixed r<max(m,n), one step already suffices.

## Search scope and limits

Queries included deep-linear observability, training/observational equivalence, identifiable Gram matrices, NTK Kronecker sums, finite-step/continuous symmetry, and two-step linear-network dynamics. Several generic identifiability results concerned static factorization, data reconstruction or recurrent networks and did not answer this experiment. No systematic citation-network search across all control/realization literature was completed. The conclusion does not infer global priority from nonappearance in these queries. Primary texts above were inspected directly; secondary summaries were not used to assign theorem priority.
