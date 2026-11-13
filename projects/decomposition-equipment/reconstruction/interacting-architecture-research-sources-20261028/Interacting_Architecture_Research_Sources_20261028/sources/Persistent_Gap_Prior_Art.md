# Prior-art audit: bounded-rank joint process with simple HMM marginals

**2026-10-28 UTC. Verdict:** the stated existence phenomenon is already an elementary consequence of the classical binary probability clock plus an XOR masking construction. The Lorentz boost/reflection family may be a useful explicit benchmark, but the combination “rank three + fixed paired binary alphabet + bounded/simple marginals + unbounded or infinite joint positive-realization size” does not by itself support a substantive novelty claim.

## 1. Strongest directly verified baseline

[Herbert Jaeger, *Observable Operator Models for Discrete Stochastic Time Series* (2000), author manuscript §7, printed pp. 12–14](https://www.ai.rug.nl/minds/uploads/oom_neco00.pdf) constructs a **binary, three-dimensional probability clock** using a scaled rotation and a reset operator. Irrational rotation has no finite HMM realization. For angle \(2\pi/q\), the published paper explicitly states a finite realization exists and every HMM realization needs **at least \(q\)** states. It also uses an invariant initial state for a stationary, dimension-three clock in §9, printed p. 20. Proposition 6 gives the underlying invariant-cone/polyhedral-cone characterization.

**Important correction:** [Jaeger's 2012 author addendum](https://www.ai.rug.nl/minds/uploads/addendumProbClock.pdf) says the original reset vector \((0.75,0,0.25)^T\) is invalid for some rotation angles: it can yield negative word probabilities. The replacement \((0.9,0,0.1)^T\) gives valid OOMs for every angle and retains irrational-angle non-HMM behavior. Use this correction when claiming a family indexed by arbitrary \(q\), not merely one valid angle.

[Grinberg and Precup, *Average Reward Optimization Objective in Partially Observable Domains* (ICML 2013), §4.2](https://proceedings.mlr.press/v28/grinberg13.pdf) independently uses the same binary, dimension-three clock baseline for large/infinite HMM-state requirements and extends it to controlled examples. Their stronger exact-state-count wording should not be silently substituted for the conservative lower bound in Jaeger's published source; their displayed parameters also predate incorporation of the correction.

These are primary author/research sources. A targeted search did **not** identify a published theorem with the exact two-channel mask formulation below. That is a search limitation, not evidence of originality: the reduction is short and removes the need for a sophisticated joining theorem.

## 2. Elementary mask-lift lemma: stronger marginals than requested

The following is an explicit deduction in this audit, **not** attributed as a verbatim theorem to those papers.

Let \(Z=(Z_t)\) be any stationary binary process. Let \(U=(U_t)\) be iid fair bits independent of the entire process \(Z\), and define
\[
X_t=U_t,\qquad Y_t=U_t\oplus Z_t.
\]
Then
\[
\Pr(X_{1:n}=x,Y_{1:n}=y)
=2^{-n}\Pr(Z_{1:n}=x\oplus y).
\]

Consequences:

* **Both marginals are iid fair.** For every word \(y\), summing over \(x\) gives \(2^{-n}\); the same holds for \(X\). Each marginal has a one-state HMM, better than “at most eight.”
* **Stationarity is preserved.** The construction commutes with time shift and starts from the stationary product law of \(U,Z\).
* **Linear predictor/Hankel rank is exactly preserved.** If \(Z\) has operators \(T_0,T_1\), the joint process has \(S_{xy}=\tfrac12T_{x\oplus y}\) with unchanged boundary vectors. Hence joint rank is at most source rank. Conversely, \(T_z=\sum_{x\oplus y=z}S_{xy}\), so projecting the pair back to \(Z\) proves the opposite inequality. In particular, source rank three gives joint rank three.
* **Unrestricted positive-realization size is preserved.** Any joint nonnegative edge-emitting realization projects to \(Z\) by summing symbol operators, with no extra states. Conversely, splitting each source symbol operator in half constructs the pair realization with no extra states. The same equality of minimum state counts holds within the ordinary state-emitting HMM convention when arbitrary joint output distributions are allowed: set \(p(x,y\mid h)=\tfrac12p_Z(x\oplus y\mid h)\).
* **One-time pair complexity is automatically at most two.** Every \(2\times2\) nonnegative probability matrix is a sum of at most two nonnegative rank-one matrices, by its rows. This condition therefore adds no restriction to *any* paired-binary benchmark.

Applying this lift to the corrected probability clock establishes exactly the requested qualitative gap: fixed alphabet four, stationary rank three, one-state marginal HMMs, arbitrarily large finite joint positive realization for rational angles, and no finite joint realization for irrational angles.

**Architectural caveat.** Given the source hidden mode alone, the mask-lift pair emissions need not be conditionally independent. If independent local emissions are required, include the current mask bit in the hidden mode; this costs a factor at most two for a state-emitting source model. The projection lower bound still applies. State-emitting and edge-emitting minimum state counts should not be identified across conventions.

## 3. Checkable stationary corrected-clock template

For clarity, the following stationary specialization is another audit deduction from the corrected clock, not a claimed quotation. In column convention let
\[
\ell=(1,1,1),\quad v=(9/10,0,1/10)^T,\quad
A=\tfrac12\operatorname{diag}(1,R_\theta),\quad B=v\ell(I-A),
\]
and
\[
s=\frac{(I-A)^{-1}v}{\ell(I-A)^{-1}v}.
\]
Then \(\ell(A+B)=\ell\), \((A+B)s=s\), and \(\ell s=1\).

The cone \(C=\{(x,y,z):x\ge9\sqrt{y^2+z^2}\}\) is invariant under \(A\). Also \(\ell(I-A)\) is strictly positive on \(C\setminus\{0\}\): its spatial coefficient norm is at most \(3\sqrt2/2\), whereas its axial contribution is \(x/2\). Thus \(B\) maps \(C\) into the ray through \(v\), and all word probabilities are nonnegative. The geometric series for \((I-A)^{-1}v\) places \(s\) in \(C\).

For \(\theta\not\equiv0,\pi\), the orbits \(A^ns\) and \(\ell A^n\) each span dimension three, verifying minimal linear rank three. Rational \(\theta=2\pi/q\), \(q\ge3\), preserves the polygonal cone generated by the \(q\) rotations of \(v\), yielding a finite nonnegative edge realization. Any full-dimensional pointed polyhedral invariant cone must have at least \(q\) rays: rotation permutes its extreme rays, and every nonaxis ray has orbit size \(q\). Irrational angle forces rotational symmetry and infinitely many extreme rays. This recovers the standard positive-realization obstruction without relying on the original uncorrected numeric example.

## 4. Novelty boundary for the proposed Lorentz family

**Already explained by the baseline:** unbounded hidden-state cost at fixed rank; rational-versus-irrational dichotomy; fixed paired-binary alphabet; simple finite-state marginal processes; bounded single-time product-mixture count; stationary examples.

**Potential additional content requiring explicit hypotheses and proof:**

1. Both marginals are genuinely temporally nontrivial, perhaps each with full predictor rank three; the iid mask lift does not establish that stronger condition.
2. The joint process cannot be reduced to a single hard scalar channel by any admissible spatial frame or symbol recoding. XOR recovers the entire hard process in the simple lift; unknown-frame claims must specify whether that recoding is allowed.
3. A precise interacting-architecture obstruction, not just a general nonnegative-realization obstruction, that separates independently feasible persistent realizations from a common constrained realization.
4. A finite-data, robust, quantitative certificate stronger than “eventually some arbitrarily long word distinguishes models.” Exact rational/irrational spectra alone are fragile as statistical evidence.
5. An independently useful structural classification or a strict comparison against the mask-lift baseline.

The proposed alternating-word formula
\[
c^{2n}\bigl(\cosh^2\eta-\sinh^2\eta\cos(n\theta)\bigr)
\]
has the familiar three exponential modes \(c^2,c^2e^{i\theta},c^2e^{-i\theta}\). Its peripheral-spectrum obstruction is therefore in the same positive-realization family; merely relocating the rotation into a two-letter product does not establish a new principle. This audit has not checked the full proposed Lorentz model's validity, marginal realizations, or minimality.

**Recommended positioning:** “An explicit interacting benchmark refining the classical probability-clock separation,” with the exact refinement named. Do not claim discovery of the general marginal-versus-joint gap. If the intended refinement excludes iid or recodable mask constructions, state that restriction before evaluating novelty.

