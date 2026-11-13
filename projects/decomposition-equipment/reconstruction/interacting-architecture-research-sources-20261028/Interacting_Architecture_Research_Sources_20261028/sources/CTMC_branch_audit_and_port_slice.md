# Uncalibrated CTMC route: exact structural statements and why it is not the main discovery theorem

Status: mathematical derivation / prior-art audit, 2026-10-27. Not a completed discovery milestone. No Lean verification.

## Plain-language abstract

Ordinary observations taken at regular time intervals can conceal what happened between observations. One possible approach is to recover every continuous-time mechanism compatible with the observations, then look for components inside each mechanism. This avoids a reset that directly reveals components. However, two substantial limitations emerged. The recovery of all compatible mechanisms is already established mathematics. More importantly, when the observed transition matrix has distinct eigenvalues, every compatible mechanism has exactly the same autonomous deterministic subsystems. Temporal ambiguity alone therefore cannot supply the intended difficult example of discovering different autonomous subsystem structures. It can still affect permitted communication and synchronization, but that is a narrower claim.

## 1. Fixed model universe

A finite-state continuous-time Markov chain with generator Q is sampled every Δ>0, giving P=exp(ΔQ). Ordinary noisy emissions may hide the states; any preceding HMM identification theorem must state its own generic rank and identifiability assumptions. Nothing below establishes that preceding step from arbitrary finite readouts. Assume P has been identified up to simultaneous state relabeling and has simple spectrum. No reset, anchor state, component partition, or local transition law is given.

A spatial architecture consists of a bijection φ:X→∏_i X_i and permitted deterministic messages μ_i:X_{-i}→M_i. Its universe is asynchronous: at a jump only one coordinate changes. The rate for i changing x_i→z_i may depend on x_i and μ_i(x_{-i}), but not on any other information. This permits genuinely interacting rates and arbitrary stationary correlations. It does not permit simultaneous multi-component jumps or hidden private states beyond X.

## 2. Established generator-branch reduction

Use row-stochastic conventions. If P has a simple negative real eigenvalue, no real logarithm exists. Otherwise positive real eigenvalues have forced real logarithms. For each nonreal conjugate pair λ_j,conj(λ_j), choose conjugate eigenvectors and an integer k_j. Every real logarithm has form

Q(k)=Q_0+Σ_j k_j J_j,

where the eigenvalues on the jth pair are (log|λ_j| ± i(arg λ_j+2πk_j))/Δ. Here J_j is the real spectral matrix acting by ±2πi/Δ on that pair and zero elsewhere. The eigenvalue 1 has logarithm zero. Therefore Q(k)1=0 automatically. Generator feasibility is precisely Q(k)_{xy}≥0 for x≠y.

Let M=−log(det P)/Δ. For any generator, M=Σ_x(−Q_xx). Gershgorin gives |Im ν|≤max_x(−Q_xx)≤M for every eigenvalue ν of Q. Consequently every candidate satisfies |arg λ_j+2πk_j|≤ΔM. There are finitely many candidate integer vectors.

This reduction is NOT new. Casanellas, Fernández-Sánchez and Roca-Lacostena, *The embedding problem for Markov matrices*, Publ. Mat.67 (2023), arXiv:2005.00818, give the generic solution and all-generator algorithm (Algorithm4.7), with sharper bounds.
Source: https://arxiv.org/abs/2005.00818

## 3. Exact interface-compatible branch slice

For a proposed φ and messages μ_i, introduce no unknown local kernels. The compatible generators are exactly the bounded integer vectors k satisfying:

(a) positivity Q(k)_{xy}≥0 for x≠y;
(b) Q(k)_{xy}=0 whenever φ(x),φ(y) differ in two or more coordinates;
(c) for each i,a,z with a≠z and external states u,v having μ_i(u)=μ_i(v),
    Q(k)_{(a,u),(z,u)}=Q(k)_{(a,v),(z,v)}.

These are explicit affine equalities and inequalities in k. If feasible, define the positive local rate by this common value. Summing the local generators reproduces Q(k) exactly, including its diagonal because row sums are zero. Conversely any architecture in this stated universe must satisfy (a)–(c). Thus interface feasibility has become a bounded integer-polytope problem, not existential unknown stochastic tensors. Failing (b) exposes a simultaneous jump; failing (c) exposes two externally indistinguishable contexts requiring different local rates.

The statement is complete ONLY conditional on a proposed state-coordinate bijection and messages. Enumerating all bijections and finite messages gives formal exhaustive discovery in a bounded universe, but does not constitute an ambitious structural discovery theorem. It is not claimed as such.

## 4. Alias-invariance theorem for autonomous deterministic quotients

**Theorem.** Suppose P has simple spectrum. For every generator Q with exp(ΔQ)=P and every partition π of X, π is strongly lumpable for P iff it is strongly lumpable for Q. Consequently all such generators have exactly the same autonomous deterministic subsystem partitions.

**Proof.** Let V_π be the subspace of real functions on X constant on each π-block. Strong lumpability is equivalent to invariance of V_π. If V_π is Q-invariant, the power series for exp(ΔQ) makes it P-invariant. Conversely, Q commutes with P. Since P has simple spectrum, every commuting matrix is a polynomial in P (interpolate its eigenvalues on P's distinct eigenvalues; realness gives a real polynomial). Thus P-invariance implies Q-invariance. ∎

The same argument works for cyclic P, whose commutant is its polynomial algebra, whenever a real logarithm exists. It does NOT establish invariance for noncyclic repeated-spectrum P.

Consequences: choosing different simple-spectrum logarithm branches cannot change whether a fixed deterministic coordinate is autonomous. Branches can still change asynchronous sparsity, exact rates, non-autonomous message requirements, or bounded resources. Do not advertise temporal aliases as an autonomous-subsystem existence counterexample in this class.

## 5. Why full Cartesian support is another potentially revealing promise

If every local move is positive in every external context, the support graph of Q is Cartesian. Its prime graph factorization recovers finest coordinate candidates; rate profiles then recover dependencies. This supports interacting dynamics, but much of architecture recognition is again supplied by a strong support promise. The construction is a useful integration baseline, not evidence of a new architecture-discovery mechanism.

Rate-dependent Cartesian compartmental constructions are explicitly discussed in *Products of Compartmental Models in Epidemiology* (2017), Appendix A: rates in one factor may depend on the other factor's state, while independent Kronecker-sum chains are only a special case.
Source: https://pmc.ncbi.nlm.nih.gov/articles/PMC5576399/
Graph-based transition-system factorization also has an existing literature:
https://ijcai.org/proceedings/2016/465

## 6. Precise remaining obstacle

The unknown-positive-frame step has not been eliminated. A predictive linear representation generally admits multiple positive state realizations; choosing a Cartesian positive frame is not the same as choosing an invariant linear subspace or factoring a transition support graph. Restricting to identifiable HMM states and full Cartesian asynchronous support bypasses that problem. A satisfactory main theorem must derive admissible positive spatial frames from observable behavior or certify their absence, with coupling/interface constraints included during discovery. The branch-slice calculation is reusable once a frame is proposed, but does not solve that task.

## 7. Two incommensurate observation intervals remove the alias issue (elementary lemma)

Suppose the SAME identified state coordinates carry transition matrices exp(tQ) and exp(sQ), with t/s irrational. If another generator R has the same two matrices, then Q=R. Indeed the two observed matrices commute, and for all integers m,n their invertible powers give exp((mt+ns)Q)=exp((mt+ns)R). The integer additive subgroup generated by t,s is dense in R. Continuity gives equality at every real time, and differentiation at zero gives Q=R. Likewise, a deterministic partition invariant under both sampled matrices is Q-invariant: its finite-dimensional invariant subspace is invariant under their inverses, then their integer products, their limits, and the derivative at zero. The same-coordinate requirement is essential; independently identified hidden-state models at the two rates need aligned state labels/gauges.

This is an elementary observation, not a claimed novel discovery theorem. It shows exactly which part of the difficulty can be observational aliasing rather than spatial decomposition.
