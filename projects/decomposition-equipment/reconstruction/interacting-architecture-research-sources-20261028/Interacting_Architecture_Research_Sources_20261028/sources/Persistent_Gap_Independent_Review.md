# Independent audit: a persistent positive-realization gap

## Verdict and scope

**The construction is valid.** The exact-rational variant has the following properties, uniformly over integers \(q\ge3\), with \(\theta=2\pi/q\):

| Quantity | Certified value / bound |
|---|---:|
| Observable linear Hankel rank | exactly 3 |
| Nonnegative rank of the **entire infinite Hankel matrix** | exactly 3 |
| One-time binary-pair nonnegative rank / product-mixture count | exactly 2 |
| Each channel's positive edge-emitting realization | at most 3 states |
| Each channel's state-emitting realization | at most 6 states |
| Joint positive edge-emitting realization | exactly \(q\) states |
| Joint state-emitting realization with deterministic, hence product, two-channel emissions | between \(q\) and \(4q\) states |

Every finite joint word has strictly positive probability, and the process is stationary. If \(\theta/(2\pi)\) is irrational, the same construction has **no finite nonnegative joint realization**, although its full infinite Hankel nonnegative rank remains 3 and the marginal bounds remain unchanged.

The crucial Perron–Frobenius argument is sound **after an explicit accessibility/coaccessibility trimming step**. A larger invisible hidden spectral radius cannot evade the lower bound. An additional strengthening is valid: the same fixed three-ray cone used to nonnegatively factor the full Hankel matrix is invariant under each channel's marginal symbol maps.

This is a rigorous stress-test separating static positive factorization from temporally compatible positive realization. It is **not** a theorem discovering unknown typed components, not evidence that a specified physical architecture is identifiable, and not a novelty claim about the underlying positive-realization mechanism.

“Positive realization” below means a finite realization by **entrywise nonnegative** matrices and nonnegative boundary vectors. It does not mean that every entry of every hidden matrix is strictly positive. Deterministic emission lifts necessarily contain zeros.

## 1. Exact construction and conventions

Use column-state dynamics. Set

\[
 \alpha=\begin{bmatrix}1\\1/8\\0\end{bmatrix},
 \qquad
 \beta=\begin{bmatrix}64/65&8/65&0\end{bmatrix},
 \qquad \beta\alpha=1,
\]

\[
 d=1/10,\qquad c=1/20,\qquad
 P=dI_3+(1-d)\alpha\beta.
\]

Then \(P\alpha=\alpha\), \(\beta P=\beta\), and \(\beta=(64/65)\alpha^T\). Define the planar reflections

\[
 F_1=\begin{bmatrix}1&0\\0&-1\end{bmatrix},\qquad
 F_2=\begin{bmatrix}\cos\theta&\sin\theta\\\sin\theta&-\cos\theta\end{bmatrix},
 \qquad R_i=\operatorname{diag}(1,F_i).
\]

Thus \(F_2F_1\) is rotation by \(+\theta\). For joint symbols \((a,b)\in\{0,1\}^2\), set

\[
 T_{00}=cR_1,\qquad T_{11}=cR_2,\qquad
 T_{01}=T_{10}=\frac12Q,
 \quad Q=P-cR_1-cR_2.
\]

Their sum is \(P\). For a chronological word \(w=s_1\cdots s_\ell\), define

\[
 T_w=T_{s_\ell}\cdots T_{s_1},\qquad p(w)=\beta T_w\alpha.
\]

The matrices \(T_s\) need not be entrywise nonnegative in these three observable coordinates. Their common cone positivity is proved next.

## 2. All words are strictly positive; normalization and stationarity

Let

\[
 \mathcal L=\{(t,z)\in\mathbb R\times\mathbb R^2:t\ge\|z\|_2\}
\]

be the Lorentz cone. Every nonzero vector in \(\mathcal L\) has positive first coordinate, so it suffices to consider \(x=(1,z)\), \(\|z\|\le1\). Put \(s=\beta x\). Then

\[
 56/65\le s\le72/65.
\]

The reflections preserve \(\mathcal L\), including its interior. Since \(d=2c\),

\[
 Qx=\left(\frac9{10}s,
 \left[\frac1{10}I_2-\frac1{20}(F_1+F_2)\right]z
       +\frac9{80}s e_1\right).
\]

The bracketed spatial operator has Euclidean norm at most \(1/5\). Therefore

\[
 \frac{\|(Qx)_{\rm spatial}\|}{(Qx)_0}
 \le \frac{1/5+(9/80)s}{(9/10)s}
 =\frac18+\frac2{9s}
 \le\frac{193}{504}<\frac12.
\]

In particular \(Q\) sends every nonzero vector of \(\mathcal L\) into its interior. The initial vector \(\alpha\) lies in the interior of \(\mathcal L\), and \(\beta\) lies in the interior of its dual cone. Every letter maps an interior state to an interior state. Hence

\[
 p(w)>0\quad\text{for every finite word }w.
\]

Consistency and normalization follow directly from

\[
 \sum_sT_s=P,\quad\beta P=\beta,\quad P\alpha=\alpha,\quad\beta\alpha=1.
\]

Summing over a right extension uses \(\beta P=\beta\); summing over a left extension uses \(P\alpha=\alpha\). The finite-dimensional distributions therefore define a stationary process. Neither empirical fitting nor a merely formal signed series is being used.

## 3. A fixed three-ray positive mechanism for either marginal

Both channels have the same marginal symbol operators, because \(T_{01}=T_{10}\):

\[
 M_0=T_{00}+T_{01}=\frac12\bigl(P+c(R_1-R_2)\bigr),
\]
\[
 M_1=T_{10}+T_{11}=\frac12\bigl(P-c(R_1-R_2)\bigr).
\]

Take the fixed equilateral-triangle cone

\[
 \mathcal K_*=
 \operatorname{cone}\left\{
 g_j=\left(1,\frac25\cos\frac{2\pi j}{3},
                 \frac25\sin\frac{2\pi j}{3}\right):j=0,1,2
 \right\}.
\]

Its cross-section has circumradius \(2/5\) and inradius \(1/5\). In particular it contains \(\alpha\), whose spatial radius is \(1/8\).

For any \(x=(1,z)\) with \(\|z\|\le2/5\),

\[
 s=\beta x\ge\frac{304}{325}.
\]

Ignoring the harmless factor \(1/2\), either marginal's image has first coordinate \(1/10+(9/10)s\) and spatial norm at most \(2/25+(9/80)s\). Their ratio is a decreasing function of \(s>0\), so

\[
 \frac{\|(M_i x)_{\rm spatial}\|}{(M_i x)_0}
 \le
 \frac{2/25+(9/80)(304/325)}{1/10+(9/10)(304/325)}
 =\frac{602}{3061}<\frac15.
\]

Thus both \(M_0,M_1\) send \(\mathcal K_*\setminus\{0\}\) into the interior of \(\mathcal K_*\), uniformly in \(\theta\). This gives a three-state nonnegative edge-emitting model for each marginal, using the explicit cone-lifting argument in Section 7. A standard output augmentation, proved there, gives a state-emitting model with at most six states.

For comparison, a coarser proof using the unit-circumradius triangle gives the bound \(193/569<1/2\). The smaller triangle above is preferable because it also supplies the full-Hankel factorization below.

## 4. Alternating words force ordinary observable rank exactly 3

Let \(w=(00)(11)\). Its word operator is

\[
 T_w=T_{11}T_{00}=c^2\operatorname{diag}(1,F_2F_1).
\]

Writing \(\lambda=c^2=1/400\), we obtain

\[
 f(n):=p(w^n)=\lambda^n\frac{64+\cos(n\theta)}{65}.
\]

If \(\theta\not\equiv0,\pi\pmod{2\pi}\), this is a nonzero linear combination of three distinct exponential sequences with bases

\[
 \lambda,\quad\lambda e^{i\theta},\quad\lambda e^{-i\theta}.
\]

The corresponding coefficients are \(64/65,1/130,1/130\), all nonzero. The scalar Hankel matrix \([f(i+j)]_{i,j\ge0}\) therefore has rank 3: its leading \(3\times3\) block is a Vandermonde–diagonal–Vandermonde factorization with three distinct bases and nonzero diagonal coefficients.

It is a submatrix of the full process Hankel matrix, obtained by restricting prefixes and suffixes to powers of \(w\). The full process already has a three-dimensional linear representation, so its Hankel rank is **exactly 3**. This applies to every \(q\ge3\) with \(\theta=2\pi/q\), and to every irrational \(\theta/(2\pi)\).

## 5. The full infinite Hankel nonnegative rank is also exactly 3

This stronger statement is correct and does not imply a three-state time-compatible positive realization.

First show that all normalized reachable vectors have spatial radius at most \(R=1/5\). The initial vector has radius \(1/8<R\), and the reflection letters preserve radius. For \(x=(1,z)\), \(\|z\|\le R\),

\[
 s=\beta x\ge\frac{64-8R}{65}=\frac{24}{25}.
\]

The residual letter satisfies

\[
 \frac{\|(Qx)_{\rm spatial}\|}{(Qx)_0}
 \le\frac18+\frac{(1/5)R}{(9/10)(24/25)}
 =\frac18+\frac5{108}
 =\frac{37}{216}<\frac15.
\]

Thus each reached state \(x_u=T_u\alpha\) belongs to \(\mathcal K_*\), since its normalized spatial point lies in the disk of radius \(1/5\), which is inside that triangle. Write

\[
 x_u=\sum_{j=0}^2 h_j(u)g_j,\qquad h_j(u)\ge0.
\]

For every future word \(v\), define

\[
 f_j(v)=\beta T_vg_j.
\]

Each \(g_j\) lies strictly inside the Lorentz cone, all the letter operators preserve its interior, and \(\beta\) is strictly positive on it. Hence \(f_j(v)>0\). Therefore the **single global factorization**

\[
 H(v,u)=p(uv)=\beta T_vT_u\alpha
 =\sum_{j=0}^2 f_j(v)h_j(u)
\]

is nonnegative for all prefixes and suffixes, not just for a chosen finite submatrix. Thus the infinite Hankel nonnegative rank is at most 3. Its ordinary rank is 3, so its nonnegative rank is **exactly 3**.

As an optional symmetric check, every \(T_s\) is symmetric and \(\beta=(64/65)\alpha^T\), so normalized future rows obey the same radius-\(1/5\) bound by reversing the word. This makes their positivity on the three rays especially transparent, but is not necessary for the factorization proof.

The missing condition is **joint-symbol shift invariance** of \(\mathcal K_*\). The triangle supports a static Hankel factorization and is invariant under both marginal symbol maps, but in general it is not invariant under the two joint reflection letters. A nonnegative factorization by itself supplies no fixed nonnegative matrices that implement every joint shift.

## 6. The Perron-period lower bound, including invisible hidden modes

Suppose there were any \(K\)-dimensional nonnegative joint realization: nonnegative letter matrices \(L_s\), initial column \(a\), and output row \(b\), reproducing all the word probabilities. This assumption is weaker than being a stochastic HMM, so a lower bound here applies to either edge-emitting or state-emitting HMMs.

For the alternating word let

\[
 N=L_{11}L_{00}\ge0.
\]

Then

\[
 bN^na=f(n)=\lambda^n\frac{64+\cos(n\theta)}{65}.
\]

### 6.1 Trim before asserting the spectral radius

Restrict \(N\) to the states that are both reachable from the support of \(a\) under powers of \(N\) and able to reach the support of \(b\) under powers of \(N\). Call the restricted matrix \(\widehat N\), with corresponding vectors \(\widehat a,\widehat b\). Every path contributing to \(bN^na\) lies wholly in this active set. Therefore

\[
 \widehat b\widehat N^n\widehat a=f(n)
\]

for every \(n\), and the retained dimension is at most \(K\).

For each retained source state \(i\) choose \(r_i\ge0\) such that
\(u_i=(\widehat N^{r_i}\widehat a)_i>0\). For each retained target state \(j\), choose \(s_j\ge0\) such that
\(v_j=(\widehat b\widehat N^{s_j})_j>0\). Nonnegativity gives

\[
 f(n+r_i+s_j)
 \ge v_j(\widehat N^n)_{ji}u_i.
\]

Since \(f(k)\le\lambda^k\), every entry obeys

\[
 (\widehat N^n)_{ji}
 \le \frac{\lambda^{r_i+s_j}}{v_ju_i}\lambda^n.
\]

There are only finitely many entries, hence \(\rho(\widehat N)\le\lambda\). Conversely, either the growth lower bound \(f(n)\ge(63/65)\lambda^n\), or the eigenvalue argument immediately below, gives \(\rho(\widehat N)\ge\lambda\). Thus

\[
 \boxed{\rho(\widehat N)=\lambda.}
\]

This is the needed repair to an otherwise incomplete argument. The original untrimmed matrix may indeed have a larger unreachable or unobservable spectral radius; it is irrelevant after this step. There is no cancellation available to conceal a larger radius inside the active nonnegative subsystem.

### 6.2 The three observable exponential bases remain eigenvalues

Let \(m(z)\) be the characteristic polynomial of \(\widehat N\). Cayley–Hamilton implies that \(f(n)\) obeys the recurrence with polynomial \(m\). Substituting its expression as a sum of three distinct exponentials and using their linear independence shows

\[
 m(\lambda)=m(\lambda e^{i\theta})=m(\lambda e^{-i\theta})=0.
\]

Thus the complex pair is genuinely in the spectrum of the active nonnegative matrix, and is peripheral because its modulus equals \(\rho(\widehat N)\).

### 6.3 Rational period and irrational impossibility

Put \(\widehat N\) in Frobenius block-triangular form. The eigenvalue \(\lambda e^{i\theta}\) belongs to an irreducible diagonal block. Its radius must be \(\lambda\): it is at least the modulus of this eigenvalue and at most the radius of \(\widehat N\). Perron–Frobenius theory says the peripheral eigenvalues of an irreducible nonnegative block of period \(h\) are its Perron root times the \(h\)-th roots of unity; its \(h\) cyclic classes imply \(h\) is no larger than its dimension. See [Mike Boyle, *Notes on the Perron–Frobenius Theory of Nonnegative Matrices*, Theorem 3.9 and Section 3](https://math.umd.edu/~mboyle/papers/pfnotes.pdf).

For \(\theta=2\pi/q\), the phase is a primitive \(q\)-th root. Hence \(q\mid h\), and

\[
 \boxed{K\ge\dim(\text{active block})\ge h\ge q.}
\]

For irrational \(\theta/(2\pi)\), the phase is not any root of unity, contradicting the same theorem. Therefore **no finite nonnegative joint realization exists**.

The conclusion also applies to rational \(\theta=2\pi p/q\) in lowest terms, with denominator \(q\), excluding the degenerate ranks at \(q=1,2\).

## 7. Rational upper bounds, including small polygons and stationary lifting

### 7.1 The \(q\)-gon cone works for every \(q\ge3\)

For \(\theta=2\pi/q\), set

\[
 \mathcal C_q=\operatorname{cone}\{v_j=(1,\cos(2\pi j/q),\sin(2\pi j/q)):j=0,\ldots,q-1\}.
\]

The cross-section contains the disk of radius \(\cos(\pi/q)\ge1/2\) and is contained in the unit disk. Reflection \(F_1\) maps vertex \(j\) to \(-j\), and reflection \(F_2\) maps it to \(1-j\), modulo \(q\). Thus both reflection letters preserve \(\mathcal C_q\).

Section 2 shows that \(Q\) sends all of \(\mathcal L\setminus\{0\}\) into spatial radius at most \(193/504<1/2\), and hence into the interior of \(\mathcal C_q\). The initial spatial radius \(1/8\) is also below every polygon's inradius. Thus all four letters preserve \(\mathcal C_q\), and \(\alpha\in\mathcal C_q\). The case \(q=3\), which has the smallest inradius, is explicitly covered; no large-\(q\) approximation is being used.

### 7.2 Normalize generators to obtain a stochastic edge realization

This elementary construction applies both to \(\mathcal C_q\) and to the marginal cone \(\mathcal K_*\). Suppose a cone has \(k\) generators \(v_j\), is preserved by all letter maps, contains \(\alpha\), and \(\beta v_j>0\). Normalize

\[
 g_j=\frac{v_j}{\beta v_j},\qquad G=[g_1\ \cdots\ g_k],\qquad\beta G=\mathbf1^T.
\]

For each letter \(s\) and generator \(j\), choose nonnegative coefficients expressing \(T_sg_j\) in these generators. Collect them into \(L_s\ge0\), so

\[
 GL_s=T_sG.
\]

Writing \(\widetilde P=\sum_sL_s\), the normalization gives

\[
 \mathbf1^T\widetilde P=\beta G\widetilde P=\beta PG=\beta G=\mathbf1^T.
\]

Thus \(\widetilde P\) is column-stochastic. Choose \(\pi\ge0\) with \(G\pi=\alpha\); automatically \(\mathbf1^T\pi=1\). Intertwining then gives

\[
 \mathbf1^TL_w\pi=\beta T_w\alpha=p(w).
\]

To ensure a stationary hidden initial distribution, consider the nonempty compact convex fiber

\[
 \mathcal F=\{\pi\ge0:G\pi=\alpha\}.
\]

It lies in the probability simplex because \(\beta G=\mathbf1^T\). The stochastic matrix \(\widetilde P\) maps the fiber into itself, since \(G\widetilde P\pi=P\alpha=\alpha\). Cesàro averaging iterates of any point in this fiber and taking a convergent subsequence yields \(\pi_*\in\mathcal F\) with \(\widetilde P\pi_*=\pi_*\). Hence a stationary lift exists; choosing an arbitrary cone decomposition of \(\alpha\) without this argument would not itself establish hidden stationarity.

For the joint process, \(k=q\); combined with Section 6, the minimum edge-emitting state count is exactly \(q\). For either marginal, \(k=3\).

### 7.3 Explicit state-emitting output augmentation

Given a stationary edge model \(\{L_s\}\) with \(k\) states and alphabet size \(m\), use \(mk\) states \((i,s)\), where \(i\) is the destination state of the preceding edge and \(s\) is that edge's emitted symbol. Define

\[
 W_{(i,s),(j,t)}=(L_s)_{ij},\qquad
 \mu_{(i,s)}=(L_s\pi_*)_i.
\]

The matrix \(W\) is column-stochastic, and

\[
 W\mu=\mu,
\]

because \(\sum_sL_s\pi_*=\pi_*\). Emit symbol \(s\) deterministically in state \((i,s)\), then transition using \(W\). The probability of an emitted word is exactly

\[
 \mathbf1^TL_{s_\ell}\cdots L_{s_1}\pi_*.
\]

For joint binary symbols, the state is \((i,a,b)\); the two deterministic outputs are conditionally independent given the state. This gives at most \(4q\) joint state-emitting states. For a binary marginal, it gives at most six. The product-emission statement is therefore verified with the intended common-state timing, not with a mixed-time or edge-conditional interpretation.

## 8. The single-time positive factorization is trivial and exact

The one-time joint probability matrix has entries

\[
 p_{00}=c,\qquad
 p_{11}=c\frac{64+\cos\theta}{65},\qquad
 p_{01}=p_{10}=\frac{1-p_{00}-p_{11}}2.
\]

All are strictly positive. Any nonnegative \(2\times2\) table has a two-component product mixture by conditioning on its first coordinate. Here its rank is exactly 2: \(p_{00},p_{11}\le1/20\) while \(p_{01}=p_{10}\ge9/20\), so its determinant is strictly negative. Hence its nonnegative rank / minimal product-mixture count is exactly 2, independent of \(q\).

This one-time claim is much weaker than the full-Hankel nonnegative-rank-3 result, which is the sharper static-versus-persistent comparison.

## 9. Relation to the original Lorentz-boost formulation

The originally proposed formulation is also valid, assuming the same two reflection axes as in Section 1. Let

\[
 \eta=1/10,\qquad
 S=\begin{bmatrix}\cosh\eta&\sinh\eta&0\\\sinh\eta&\cosh\eta&0\\0&0&1\end{bmatrix},
 \quad P_0=\operatorname{diag}(1,d,d),
\]

\[
 A=cSR_1S^{-1},\qquad B=cSR_2S^{-1},
 \quad T_{00}=A,\ T_{11}=B,\ T_{01}=T_{10}=(P_0-A-B)/2,
 \quad\alpha_0=e_0,\ \beta_0=e_0^T.
\]

Its alternating sequence is indeed

\[
 p(w^n)=c^{2n}\bigl(\cosh^2\eta-\sinh^2\eta\cos(n\theta)\bigr).
\]

The three nonzero exponential coefficients still imply rank 3, and the scalar factor is bounded above and bounded away from zero. Thus exactly the same trimmed Perron argument proves the \(q\)-state lower bound and irrational impossibility.

For positivity and upper bounds, change coordinates by \(S^{-1}\) and rescale boundary vectors to

\[
 \alpha'=(1,-\tanh\eta,0)^T,
 \qquad\beta'=(\cosh^2\eta,\cosh\eta\sinh\eta,0).
\]

Then \(\beta'\alpha'=1\), and the transformed total matrix is

\[
 P'=dI+(1-d)\alpha'\beta'.
\]

This is the same cone-proof template as above, with spatial initial radius \(\tau=\tanh\eta<1/10\). On the unit Lorentz cross-section, \(s=\beta'x\) is at least

\[
 s_{\min}=\cosh\eta\,e^{-\eta}=(1+e^{-1/5})/2>9/10.
\]

The residual ratio is bounded by

\[
 \tau+\frac2{9s}<\frac1{10}+\frac{20}{81}<\frac12.
\]

Thus the rational \(q\)-gon construction works for every \(q\ge3\), and strict positivity holds. For the marginal maps the ratio is bounded by

\[
 \frac{1/5+(9/10)\tau s}{1/10+(9/10)s}
 <\frac{281}{910}<\frac12,
\]

so even the original boost version admits a fixed triangle cone and at most **six**, rather than merely eight, state-emitting marginal states. The proposed eight-state marginal bound was safe but not sharp.

The exact-rational version is a separate convenient parametrization, not literally the same process as the boost version: the alternating cosine coefficient changes sign. All claims about the **particular full-Hankel factorization and shared small triangle** in Sections 3–5 were established explicitly for the rational version. No unsupported identification of the two processes is needed.

## 10. Necessary qualifications

1. **Finite data.** These are exact infinite-word/process statements. Near-irrational and high-denominator rational parameters cannot be distinguished reliably from arbitrary finite noisy data without a statistical separation assumption. No robust finite-sample architecture-identification theorem follows.
2. **Nonnegative versus strictly positive hidden entries.** All observed word probabilities are strictly positive. The finite hidden realizations may have zeros, as deterministic output lifts and periodic Perron blocks naturally do.
3. **Count the right object.** Joint edge states are exactly \(q\); joint same-state product-emission states are only bounded between \(q\) and \(4q\). The three-dimensional observable space and three-factor Hankel decomposition are not three hidden modes with time-compatible positive mechanisms.
4. **Local processes do not identify a physical decomposition.** The two marginal laws are individually simple and in fact identical in this example. That alone does not identify separate physical components, their types, or the causal wiring of a joint system.
5. **Classical obstruction, useful benchmark.** The mechanism is the incompatibility between persistent finite nonnegative dynamics and an arbitrarily high-order or irrational peripheral rotation. The construction is a clean benchmark for the missing shift-compatibility requirement, not a claimed new general discovery mechanism.

## Verification record

The proof uses exact rational bounds \(193/504\), \(193/569\), \(37/216\), and \(602/3061\). The small-polygon threshold is the exact inradius lower bound \(\cos(\pi/q)\ge1/2\) for \(q\ge3\). The invisible-spectrum issue is handled explicitly rather than assuming that every hidden eigenvalue is observable. The only standard spectral theorem invoked externally is the peripheral-spectrum statement for irreducible nonnegative matrices, with a primary academic reference supplied in Section 6.
