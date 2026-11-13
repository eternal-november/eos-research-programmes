# Prior-art comparison: exact two-sided linear KI informativity

2026-10-30. Bounded comparison of the two-sided linear evidence criterion with primary sources; not a priority determination. The optional inverse-domain guard is discussed separately below.

## Bottom line

The proof is a **specific exact, constructive full-block uncertainty criterion for a prescribed linear readout under kernel-image feedback**. The nearest verified sources are considerably closer than generic version-space safety: classical two-sided matrix equations; universal rank/range conditions for `A+BXC`; uniform structural-informativity rank tests; and the kernel-image partial trace itself.

I did not find the exact F1/F2 plus O1/O2 branching criterion in these inspected sources. Equally, I have not proved that the whole criterion is a direct corollary of one cited theorem. Appropriate status: **a useful derived exact criterion, with substantial classical overlap and unresolved priority**. Neither 'just the generic definition of informativity' nor 'new general evidence-composition theory' accurately describes the current result.

## 1. Completion-space parametrization: classical, exact match

The evidence equations are the simultaneous matrix equations `HF=R` and `F I_S=C_S`. Penrose's 1955 *A generalized inverse for matrices*, Corollary 2, gives consistency of `AX=C, XB=D` iff the individual equations are consistent and `AD=CB`; the paper attributes this result to Cecioni. Applying the homogeneous equations yields the familiar freedom with image in ker H and vanishing on S. Thus `F=F0+i_K Zq` is the coordinate-free form of classical two-sided matrix interpolation, not a new parameterization.

Primary: https://faculty.kfupm.edu.sa/math/jaafarm/lec-notes/Moore-Pinrose.pdf (p. 409, Theorem 2 and Corollary 2).

## 2. Full-block rank/range uncertainty: closest algebraic baseline

Tian–Cheng (2003), *The maximal and minimal ranks of A−BXC with applications*, Theorems 2.4 and 2.5 give the unrestricted extremal ranks; Corollary 2.9 characterizes rank invariance, and Corollary 2.10 characterizes both column- and row-range invariance. Theorem 2.14 treats perturbations constrained by fixed left/right annihilators, directly matching the geometry of two-sided evidence. These are arbitrary-field algebraic statements in the paper's notation. Tian's later rank-constrained paper also treats perturbations of specified rank.

Primary: https://nyjm.albany.edu/j/2003/9-18.pdf . Later primary: https://optimization-online.org/wp-content/uploads/2012/04/3426.pdf .

**Precise comparison, derived here:** writing i_U:U→V, the mission is equivalent to the simultaneous universal identities

    rank L_Z = rank(L_Z i_U),
    rank [L_Z; E_Z] = rank L_Z.

The first is solvability of the internal equation for every external input; the second is observed-value uniqueness/prescription on all fixed points. Crucially, these compare correlated matrices evaluated at the SAME Z. Subtracting independently optimized ranks would not establish them. The checked rank-extremum theorems therefore provide close tools, not yet a demonstrated one-line reduction of the complete criterion. The O2 branch's simultaneous multiplier `(DL0=E0, DB=C)` is stronger information than a mere numerical rank test, while O1 correctly isolates the untested-feedback-inaccessible branch.

## 3. Structural data informativity: close proof mechanism, different mission

Eising–Trentelman (2021), *Informativity of noisy data for structural properties of linear systems*, studies an affine matrix family `QAP=R`. Theorem 4 supplies a uniform Rosenbrock-rank criterion; later results specialize it to observability/detectability, controllability/stabilizability, and invertibility. Its necessity proof modifies a matrix to map a prescribed real vector to a desired residual while retaining the evidence constraint. That modification can be chosen rank one in the real-vector step. Thus finite algebraic tests and low-rank adverse completions are established proof mechanisms.

The paper's dynamical model fixes B,C,D and noise channels, leaving A unknown. It does not state the inspected criterion for simultaneous uncertainty in internal and mission-readout rows, a fixed algebraic feedback policy, and a prescribed map J under nonunique hidden fixed points. No direct reduction was verified here.

Primary: https://arxiv.org/html/2010.15564 (§III, Theorem 4 and proof); published primary: https://www.math.rug.nl/~trentelman/psfiles/Info_properties_noisy.pdf . **Authors are Jaap Eising and Harry Trentelman.**

## 4. KI feedback versus strict inverse feedback

MSS Definition 3.15, Remark 3.16, Proposition 3.17 give the kernel-image trace and its partial-trace axioms. For a fixed block operator, existence of solutions for each external input plus independence of the observed output from the hidden solution is precisely its image/kernel condition, applied to the mission readout. This does not require all hidden fixed points to be unique. The source does not give the present universal-over-evidence completion criterion or its positive/negative witness extraction.

Primary: https://arxiv.org/html/1107.3608#S3.SS3.SSS3 .

The optional strict inverse-domain guard is a direct full-block nonsingularity calculation. With nominal D0 invertible, put Q=q_U D0^{-1}B. If Q=0, the determinant lemma makes every update D0−BZq_U invertible. If Q≠0, choose k with Qk≠0 and a functional ℓ with ℓ(Qk)=1; the rank-one Z=kℓ makes the update singular. Thus this optional guard is an elementary special case of universal full-block rank/invertibility analysis, not a new feedback principle. The prescribed-output test that follows it must remain separate from KI: it intentionally rejects missions with allowed unobservable/nonunique internal fixed points.

## 5. What the positive result adds within the stated scope

The proof gives explicit sections, coherent changes between section choices, and an honest mission factorization from a **checkable finite evidence certificate**, rather than assuming a global joint cylinder. That is genuine progress beyond the conditional structural comparison theorem. Section dependence on the hidden completion is an existence witness, not a change of policy. The shear formula is the standard algebra of changing splittings of a surjection; its cocycle identity is immediate from the square-zero correction, so the shear should not itself carry a novelty claim.

The result still concerns one specified feedback experiment with exact linear row/column evidence and arbitrary full-block residual uncertainty. It does not imply closure of that evidence class under multi-box composition, physical acquisition guarantees, inequality-based robust control, independent safety guards, or all heterogeneous missions. Generic composition yields rational/shared uncertainty. Keeping the same parameter across internal and observed outputs is essential, but that soundness requirement alone is also established in full-block uncertainty analysis.

## Recommended attribution sentence

“We derive an exact finite-dimensional criterion for this two-sided experimental model and fixed kernel-image feedback mission, using classical matrix-completion and rank/kernel ideas. Its precise relation to existing universal rank and informativity results remains under review; no novelty or general network-closure claim is made.”
