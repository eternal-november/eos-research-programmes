# Persistent positive assembly obstruction

## Result and research boundary

The reflection construction below is a valid stationary, fully supported, two-channel process. For a rational angle of order q, its smallest edge-emitting finite hidden Markov realization has exactly q states. For an irrational angle it has none. Nevertheless each entire one-channel process has a three-state edge-emitting realization, every single-time spatial cut has nonnegative rank at most two, and the **entire infinite past–future Hankel matrix has nonnegative rank exactly three**, independently of q. All four observed-symbol operators are invertible: no observed word resets the predictive state.

This is an exact failure of static nonnegative factorization to supply persistent positive mechanisms. It is not an architecture-discovery theorem or an established novelty claim. Its spectral and invariant-cone ingredients are classical. In particular, it does not recover unknown physical components, establish a privileged spatial partition, or eliminate a common latent driver. The useful conclusion is narrower: even a single simultaneous nonnegative factorization of the complete Hankel matrix can fail the shared shift-invariance requirement.

The user’s target remains stronger: infer unknown component domains and positive local mechanisms from raw dependencies, with a compatible joint realization and explicit alternatives, rather than validate mechanisms or partitions supplied in advance. The final section identifies the unclosed step.

## Explicit process

Columns represent predictive states; a row evaluates probabilities. Let

\[
 a=(1,1/8,0)^T,\qquad b=(64/65,8/65,0),\qquad ba=1,
\]

\[
 d=1/10,\quad c=1/20,\quad P=dI+(1-d)ab.
\]

For an angle \(\theta\not\equiv0\pmod{2\pi}\), define

\[
 F_1=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
 F_2=\begin{pmatrix}\cos\theta&\sin\theta\\
 \sin\theta&-\cos\theta\end{pmatrix},\qquad R_i=\operatorname{diag}(1,F_i).
\]

The observed symbol is a pair \((X_t,Y_t)\in\{0,1\}^2\). Put

\[
 T_{00}=cR_1,\qquad T_{11}=cR_2,\qquad
 T_{01}=T_{10}=\tfrac12D,\qquad D=P-cR_1-cR_2.
\]

For a word \(w=s_1\cdots s_n\), set \(T_w=T_{s_n}\cdots T_{s_1}\) and \(p(w)=bT_wa\). The identity \(\sum_sT_s=P\), together with \(Pa=a\) and \(bP=b\), proves both cylinder consistency and stationarity once positivity is checked.

These are not entrywise nonnegative matrices. Their role is an observable linear realization. Positivity of the stochastic process must be proved separately; it is not inferred from matrix entries.

## Positivity and the stronger static factorization bound

For \(r>0\), write

\[
 K_r=\{(t,z)\in\mathbb R\times\mathbb R^2:t\ge0,\ \|z\|_2\le rt\}.
\]

Take \(r=1/5\). Both \(a\) and the transpose of \(b\) belong to \(K_r\). Each \(R_i\) and its transpose preserve \(K_r\). Because \(d=2c\),

\[
 D=\operatorname{diag}(0,B)+(9/10)ab,
 \qquad B=dI_2-c(F_1+F_2),\quad \|B\|_2\le1/5.
\]

For \(x=(t,z)\in K_r\), \(t>0\), put \(s=bx\). Then

\[
 s\ge \frac{64-8r}{65}t=\frac{24}{25}t,
 \qquad (Dx)_0=\frac9{10}s,
\]

and therefore

\[
 \frac{\|(Dx)_{\rm sp}\|_2}{(Dx)_0}
 \le\frac18+\frac{(1/5)r}{(9/10)(24/25)}
 =\frac{37}{216}<\frac15.
\]

The transpose has the same bound. Indeed, for \(y=(t,z)\in K_r\), \(a^Ty\ge(1-r/8)t\), and

\[
 (64/65)(1-r/8)=24/25,
 \qquad \frac{b_1}{b_0}=1/8.
\]

Thus every \(T_s\) and \(T_s^T\) preserves \(K_r\). Every nonzero vector in this cone pairs strictly positively with every other nonzero vector in it. Consequently every finite word has strictly positive probability.

Let \(g_1,g_2,g_3\) be the three rays with time coordinate one and spatial coordinates at the vertices of an equilateral triangle of circumradius \(2r=2/5\). Its inradius is \(r\). Hence every reachable vector \(T_wa\in K_r\) has nonnegative barycentric coordinates \(\lambda_j(w)\) in these rays. Every effect \(bT_v\), transposed, belongs to \(K_r\), so

\[
 bT_vg_j\ge (bT_v)_0(1-2r^2)>0.
\]

Therefore the **infinite** Hankel matrix has the explicit factorization

\[
 H_{v,w}=p(wv)=bT_vT_wa
 =\sum_{j=1}^3 \underbrace{bT_vg_j}_{\ge0}
 \underbrace{\lambda_j(w)}_{\ge0}.
\]

Its nonnegative rank is at most three. For \(\theta\not\equiv0,\pi\pmod{2\pi}\), the rank-three scalar subsequence in the next section proves ordinary rank at least three. Thus both ranks equal three. This controls every finite temporal cut simultaneously, not just a selected finite truncation. It does **not** assert bounded nonnegative rank for arbitrary noncontiguous spatial–temporal cuts.

The triangle is not invariant under both reflected symbol operators when their product has sufficiently large order. Its factors give valid latent labels for a static cut, not a state space on which the same positive transition matrices act at every time.

## The persistent state lower bound

For the two-symbol word \(z=(00)(11)\), \(R_2R_1\) is rotation through \(\theta\) in the spatial plane. Direct multiplication gives

\[
 f_n:=p(z^n)=c^{2n}\frac{64+\cos(n\theta)}{65},\qquad n\ge0.
\]

For nonexceptional \(\theta\), this sequence has three distinct poles
\(c^2,c^2e^{i\theta},c^2e^{-i\theta}\), all with nonzero coefficients.

Suppose a K-state edge-emitting HMM realizes the full process. For its nonnegative word matrix \(M=M_{11}M_{00}\) and initial distribution \(\pi\),

\[
 f_n=\mathbf1^TM^n\pi.
\]

Discard states inaccessible from \(\pi\) by powers of \(M\). This trimming is important: arbitrary unused positive eigenmodes cannot be used to evade the spectral argument. For every remaining state j there is a k with \((M^k\pi)_j>0\). Since all terms are nonnegative,

\[
 f_{m+k}\ge (M^k\pi)_j\,\mathbf1^TM^me_j.
\]

The explicit upper bound \(f_n\le c^{2n}\) implies that every remaining column sum of \(M^m\) is bounded by a constant times \(c^{2m}\). Hence \(\rho(M)\le c^2\). The lower bound \(f_n\ge(63/65)c^{2n}\) gives the reverse inequality. Therefore \(\rho(M)=c^2\).

The noncanceled pole \(c^2e^{i\theta}\) must be an eigenvalue of \(M\). It lies in an irreducible diagonal block with spectral radius \(c^2\). By the peripheral-spectrum theorem for an irreducible nonnegative matrix, \(e^{i\theta}\) is an h-th root of unity, where the block’s period satisfies \(h\le K\).

It follows that:

* if \(\theta/(2\pi)\) is irrational, no finite positive realization exists;
* if \(\theta=2\pi p/q\), with \(p,q\) coprime and \(q\ge3\), every positive realization has \(K\ge q\).

This proves failure of *any* fixed finite total memory budget, regardless of how that memory is partitioned into components or how instantaneous finite interfaces are wired. For component state sizes \(k_i\) and persistent interface states of sizes \(m_e\), the necessary bound is \(q\le\prod_i k_i\prod_e m_e\). Interfaces carrying memory must be counted; allowing an unbounded external clock or shared latent state invalidates the stated budget.

For each fixed budget K there is also a finite exact witness: matching \(f_n\) for \(0\le n\le K+2\) would force a K-state candidate to match every \(f_n\). The difference sequence has a linear representation of dimension at most \(K+3\); Cayley–Hamilton propagates its first \(K+3\) zero values to all later values. Thus when \(q>K\), some cylinder of length at most \(2(K+2)\) already disagrees. This is an exact-law assertion, not a noise-robust statistical test.

## Matching rational upper bound and local realizations

For \(\theta=2\pi p/q\), let \(C_q\) be the cone on the regular q-gon with vertices \((1,\cos(2\pi j/q),\sin(2\pi j/q))\). Its section contains the disk of radius \(\cos(\pi/q)\ge1/2\). Both reflections preserve it. The initial state a lies inside it, and b is strictly positive on it.

For any normalized generator \(x=(1,z)\), \(\|z\|=1\), write \(s=bx\ge56/65\). Then

\[
 (Dx)_0=(9/10)s,\qquad
 \|(Dx)_{\rm sp}\|\le1/5+(9/80)s,
\]

so

\[
 \frac{\|(Dx)_{\rm sp}\|}{(Dx)_0}
 \le\frac18+\frac{1/5}{(9/10)(56/65)}
 =\frac{193}{504}<\frac12.
\]

Hence D preserves \(C_q\). Expressing every image of a cone ray as a nonnegative combination of rays gives a q-state positive realization. Normalize each ray to have b-value one; then the sum of the lifted symbol matrices is column-stochastic because \(bP=b\). A stationary hidden initial distribution exists: start with any lift of a and take a Cesàro limit under the lifted total transition. Its projection remains a. This gives an exact q-state stationary edge-emitting HMM and proves that the preceding lower bound is sharp.

Each individual channel has operators

\[
 M_0=\tfrac12[P+c(R_1-R_2)],\qquad
 M_1=\tfrac12[P-c(R_1-R_2)].
\]

These preserve the fixed triangular cone \(C_3\), independently of \(\theta\). On a normalized vertex, with \(s=bx\ge56/65\), twice the output has time coordinate \(1/10+(9/10)s\) and spatial norm at most \(1/5+(9/80)s\). Their ratio is less than \(1/2\). Thus each whole marginal process has a three-state edge-emitting positive realization. The same lift-and-average argument gives a stationary hidden realization.

At a single time the joint output is a two-by-two probability table, so nonnegative rank at most two is automatic. No claim of novelty should rest on that observation. Edge-emitting and state-emitting state counts should not be conflated: the elementary conversion gives at most six states for a binary marginal and at most \(4q\) states for the four-symbol joint process.

## No observed reset

The two reflected operators are invertible. With the notation above,

\[
 \det B=\frac{d^2}{2}(1-\cos\theta),\qquad
 \det D=\frac9{10}\frac{64}{65}\det B>0.
\]

The determinant identity follows from the rank-one form of D: the only nonzero contribution involving the zero time block uses \((9/10)a_0b_0\det B\). Hence both off-diagonal symbol maps are invertible too. Every finite word map is invertible. Since reachable states span all three dimensions, no word maps all reachable projective states to one predictive state. There is no synchronizing observed reset word.

The total averaged map P is an invertible contraction toward a. Its rank-one summand is an algebraic decomposition of an *unobserved average*. It is not an observed operation available to the learner, and should not be described as one.

## Prior art and comparison with the masking baseline

The core phenomenon predates this construction. Jaeger’s original paper explicitly states the stable polyhedral-cone criterion, constructs an irrational-rotation process with no finite HMM, and gives the growing rational-order state lower bound. Its displayed probability-clock example has a resetting output symbol, unlike the invertible maps here. See [Jaeger 2000, Proposition 6 and Section 7](https://www.ai.rug.nl/minds/uploads/oom_neco00.pdf). The paper attributes the underlying characterization to Heller and subsequent refinements; the original bibliographic reference is Heller, *On Stochastic Processes Derived From Markov Chains*, Annals of Mathematical Statistics 36 (1965), 1286–1291, [DOI](https://doi.org/10.1214/aoms/1177700000). The original DOI endpoint was not accessible through the browsing tool in this pass; attribution was checked in Jaeger’s paper rather than represented as inspection of Heller’s full original text.

The same peripheral-rotation obstruction appears explicitly as Example 4 in [Benvenuti and Farina, A Tutorial on the Positive Realization Problem](https://sites.math.rutgers.edu/~sussmann/papers/res-farina-tutorial-positive-realization.pdf). Consequently the lower bound itself is not new. The broader distinction between linear observable realizations and positive or quantum realizations is also central to [Monras and Winter 2014](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TQC.2014.99).

There is a much simpler reason why easy one-channel laws cannot establish easy joint assembly. For any binary process Z, take an independent iid fair-bit process X and set \(Y_t=X_t\oplus Z_t\). Both X and Y are iid fair, while \(Z_t=X_t\oplus Y_t\) is recovered from the pair. A K-state joint HMM would therefore give a K-state HMM for Z. Conversely, a K-state realization of Z produces the joint output by fresh fair masking at each step. The positive-memory complexity is preserved. This is a one-line baseline, not a reconstruction theorem. It prevents presenting a marginal/joint complexity gap by itself as a mathematical advance.

The reflection family adds a transparent no-reset mechanism, sharp finite positive order, and static Hankel factorization audit, but those additions still do not turn it into the requested discovery result.

## What remains unresolved

Observed dependencies can identify a minimal linear predictive representation up to similarity under suitable finite-rank assumptions. They do not thereby supply a finite positive cone, a distinguished local tensor product, local state alphabets, or compatible interface semantics. A common invariant polyhedral cone is already necessary for an unstructured finite hidden realization. Component discovery demands more: a cone and local product/interface structure that work together for all temporal shifts and for all allowed, possibly crossing, spatial decompositions.

Neither independent cut factorizations nor an unrestricted global nonnegative factorization impose these simultaneous conditions. The rank-three Hankel factorization above makes that gap explicit. Simply quantifying over all nonnegative local tensors and imposing their equations is a valid existence restatement, not the missing intrinsic reconstruction criterion.

No non-tautological theorem that reconstructs the required crossing-compatible positive local structure from the raw observable operators was obtained in this pass. Nor was a family proved to have uniquely inferred interacting physical components. A common latent source is an observational alternative for the two-channel law and must remain in the output class unless additional operational restrictions exclude it. The precise blocker is the inference and classification of shared positive cones together with local tensor/interface structure, not positivity of each slice and not linear state reconstruction.

Status: the proposed obstruction is mathematically supported, including the stronger static Hankel factorization separation. The user’s architecture-discovery target remains open here; this note should be used as a necessary stress test and a warning against insufficient criteria, not as its completion.
