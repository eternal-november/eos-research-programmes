# Prior-art audit: conditional-emission multiplicative-defect bound

**Audit date:** 2026-10-28 UTC. **Verdict:** useful necessary certificate, but the proposed bound is *exactly an ordinary flattening-rank bound*. Its defect formulation is not a stronger numerical invariant. No novelty claim is supported. The substantive target must be joint positive/dynamical compatibility beyond these ranks.

## 1. Decisive algebraic reduction

Let \(E_{ab}\in\mathbb R^{r\times r}\), \(E_a=\sum_bE_{ab}\), \(E_b=\sum_aE_{ab}\), and \(\sum_{ab}E_{ab}=I_r\). Distinguish the two marginal alphabets despite the shared \(E\) notation. Set

\[
C=[E_{ab}]_{a,b},\qquad L=\operatorname{col}_aE_a,\qquad
R=\operatorname{row}_bE_b,\qquad F=C-LR.
\]

For the augmented block matrix
\[
M=\begin{pmatrix}I_r&R\\L&C\end{pmatrix},
\]
invertible block elimination gives
\[
\operatorname{rank}M=r+\operatorname{rank}F.
\]
But its first block row is the sum of the other block rows, and its first block column is the sum of the other block columns. Hence
\[
\boxed{r+\operatorname{rank}F=\operatorname{rank}C.}
\]

Under the proposed compression \(E_{ab}=A D_aD_bB\), with \(AB=I_r\), the factorization
\[
C=(\operatorname{col}_a AD_a)(\operatorname{row}_b D_bB)
\]
immediately gives \(\operatorname{rank}C\le K\). Equivalently,
\(F=(\operatorname{col}_a AD_a)(I_K-BA)(\operatorname{row}_bD_bB)\)
and \(\operatorname{rank}(I_K-BA)=K-r\). Both proofs give **the same bound**.

Moreover, \(E_{ab}=P^{-1}T_{ab}\) implies
\[
C_E=(I_{|\mathcal A|}\otimes P^{-1})C_T,\qquad
\boxed{r+\operatorname{rank}F=\operatorname{rank}[T_{ab}].}
\]
Thus inversion is unnecessary for computing the certificate. The direct \([T_{ab}]\) flattening also remains a necessary lower bound when \(P\) is singular, provided the corresponding hidden-model factorization is established. This does not validate the proposed compression automatically; that model-to-compression step still needs its own proof.

These identities are elementary deductions in this audit, not an assertion that a particular source printed this exact notation first. The underlying rank-additivity operation is standard Schur-complement elimination; a primary research reference on partitioned-matrix rank identities is [David Carlson, *Matrix Decompositions Involving the Schur Complement* (1975)](https://epubs.siam.org/doi/abs/10.1137/0128047).

**Observable interpretation.** In a full-rank past/future basis, replace each operator block by the matrix of probabilities \(p(u,(a,b),v)\). The resulting flattening has row index \((u,a)\), column index \((b,v)\), and the same rank as \([T_{ab}]\). It is a spatial/temporal crossing flattening, not a new type of rank obstruction.

## 2. Closest verified primary-source baselines

| Baseline | What the source establishes; relevance |
|---|---|
| Linear versus stochastic realization | [Schönhuth, *Equations for hidden Markov models* (2009), §5, Theorem 5.1](https://arxiv.org/pdf/0901.3749) explicitly presents the invariant-cone characterization attributed there to Heller (1965). This is the baseline for distinguishing observable linear dimension from hidden-state realization constraints. Heller's original full text was not retrieved; attribution here is expressly through Schönhuth's primary research paper. |
| Positive realization is more than finite Hankel rank | [Ohta, *On the Realization of Hidden Markov Models and Tensor Decomposition* (2020), introduction and §§3–4](https://arxiv.org/pdf/2008.11487) distinguishes quasi-realization from nonnegative HMM realization and shows why generic tensor arguments miss important nongeneric deterministic-observation cases. Do not equate observable rank, tensor rank, and minimal stochastic state count. |
| Commuting compression defect | [Koiran, *On the Uniqueness and Computation of Commuting Extensions* (2024), Lemma 3 and Proposition 4](https://arxiv.org/pdf/2401.01302) gives \([A_i,A_j]=B_jC_i-B_iC_j\), rank at most twice the extension deficit, plus joint image-space bounds for several matrices. This is directly adjacent prior art, including already-known multi-matrix compatibility reasoning. |
| Tensor rank and simultaneous diagonalizable extension | [Koiran, *On tensor rank and commuting matrices* (2020), Theorems 2 and 4](https://arxiv.org/pdf/2006.02374) relates tensor rank to commuting diagonalizable extensions; Theorem 4 gives an exact characterization when the slice span contains an invertible matrix. The same paper states and proves the Strassen commutator lower bound and cites Strassen's 1983 original. A merely unweighted common commuting dilation is therefore not a new general direction. |
| Multiple independent emission channels | [Tune, Nguyen and Roughan, *Hidden Markov Model Identifiability via Tensors* (2013), §V](https://arxiv.org/pdf/1305.0321) explicitly builds a multi-observer tensor with one factor for each independent observer and shared transition structure. This verifies that the multi-channel setup itself is established; no reliance is placed here on the full scope of their identifiability claims. |
| Conditional independence and grouped views | [Allman, Matias and Rhodes, *Identifiability of parameters in latent structure models with many observed variables* (2009)](https://arxiv.org/pdf/0809.5032) treats product mixtures and HMMs through grouped observed variables and tensor methods. More channels or regrouping alone is not an adequate novelty argument. |
| Positivity adds inequalities to rank | [Allman, Rhodes, Sturmfels and Zwiernik, *Tensors of nonnegative rank two* (2015), Theorem 1.1](https://jarhodesuaf.github.io/papers/NNrank2.pdf) characterizes nonnegative rank at most two by flattening-rank constraints **and supermodularity**. This is a concrete baseline for stronger semialgebraic constraints beyond flattenings. |
| State versus edge emissions | [Travers, *Bounds on Convergence of Entropy Rate Approximations in Hidden Markov Models* (2013), Appendix C](https://csc.ucdavis.edu/~cmg/papers/Travers.UCDPhDDissertation2013.pdf) distinguishes state-emitting and edge-emitting HMMs and discusses conversion. Equivalence of process classes does not preserve the state-count resource automatically. State emission and conditional channel independence must remain explicit in the theorem. |

## 3. Exact positivity stress test

Consider iid paired observations with one-time law
\[
J=\frac18\begin{pmatrix}
1&1&0&0\\0&1&1&0\\0&0&1&1\\1&0&0&1
\end{pmatrix}.
\]
The observable temporal realization has \(r=1\), \(P=1\), \(T_{ab}=J_{ab}\). Ordinary matrix rank is three, so the proposed certificate gives only \(K\ge3\), with defect rank two.

Yet every state-emitting model with conditional independence of the pair must have \(K\ge\operatorname{rank}_+(J)=4\). Proof: each diagonal position is positive; any two diagonal positions have at least one zero cross-position. A nonnegative rank-one summand therefore cannot cover two diagonal entries. Four are necessary, and the four-row mixture attains four. Taking independent hidden states at successive times realizes the iid process with four states.

This exact example is an audit deduction, illustrating the classical distinction formalized by [Cohen and Rothblum, *Nonnegative Ranks, Decompositions, and Factorizations of Nonnegative Matrices* (1993)](https://lab.rockefeller.edu/cohenje/assets/file/211CohenRothblumNonnegativeRanksDecompositionsFactorsNonnegativeMatricesLAA1993.pdf). It is not offered as a new discovery. It rules out sufficiency of the defect bound even in the simplest temporal setting.

## 4. What could be substantive—and what would not suffice

1. **Unknown spatial frame.** Observable-state similarity is already harmless: all blocks transform by the same similarity, leaving block rank invariant. Separate invertible changes of bases within the two output factors also preserve flattening rank. A genuinely unknown transformation mixing the factors is different: specify the admissible frame group and certify exclusion *for every frame*. A small numerical minimum over sampled frames is not such a certificate. A useful theorem would eliminate the frame parameters or provide an exact/robust global lower certificate. This audit has not established novelty for that specialized target.

2. **Several crossing channel partitions.** Taking the maximum of ordinary flattening ranks is an immediate baseline, not an extension. Adding their rank lower bounds is generally invalid because the same hidden states service all partitions. A substantive result would demonstrate that individually feasible factorizations cannot arise from **one common** set of hidden modes and compatible emissions. Compare against commuting-extension joint image constraints and coupled tensor-factorization work, e.g. [Sørensen and De Lathauwer, *Coupled Canonical Polyadic Decompositions*, Part I (2015)](https://epubs.siam.org/doi/abs/10.1137/140956853), rather than only against single-partition rank.

3. **Positive common dynamical dilation.** Strongest plausible target: same hidden stochastic transition, nonnegative normalized emission spectra, shared hidden coordinates and boundary distributions, all required temporal products, all required partitions, and any admissible unknown frame. Ordinary commuting extensions and separate nonnegative factorizations are relaxations, not sufficient substitutes. Crucially, \(A,B\) in an observable basis need not themselves be nonnegative, and \(E_{ab}\) need not be an entrywise nonnegative matrix. Applying nonnegative rank directly to gauge-dependent observable operators is unjustified; use actual probability arrays or an explicitly defined invariant positive cone.

4. **Required separation benchmark.** Produce an exact process for which the new certificate excludes \(K\) while every single-partition flattening and relevant elementary nonnegative-rank test permits \(K\); verify that the exclusion survives the admissible frame freedom. Then either prove a constructive sufficiency theorem or explicitly retain the one-sided “necessary obstruction” status. A perturbation margin/statistical certificate would be useful, but should compare against direct raw-operator/probability flattenings rather than amplify noise with \(P^{-1}\).

**Recommendation:** retain the defect lemma as a transparent re-expression of the flattening baseline; do not center the discovery claim on it. Focus the harder task on a rigorously specified common positive dynamical realization obstruction and a strict separation example. Priority remains unestablished.

