# Independent audit: restricted compact quotient certificate

## Verdict

The **linear-algebraic theorem is correct**, under the stated strong calibration assumptions. In particular:

1. Local control span plus an invertible common drift forces full hidden linear reachability, even from an arbitrary probability initial state.
2. The observable row space is a downward-closed direct sum of constant/contrast interaction spaces.
3. Its quotient tensor has **signed real CP rank exactly \(r\)**, where \(r\) is controlled Hankel rank.
4. An observationally equivalent initial law exists as a mixture of at most \(r\) product point states.

Important qualifications are necessary:

- Typically \(r=N=\prod_i d_i\), so a bound polynomial in \(r\) is not necessarily compact in the number of components.
- The CP decomposition is signed, not a nonnegative decomposition.
- Sparse replacement of the initial law need not preserve hidden stationarity.
- An exact **bit-size** theorem needs rational/algebraic input assumptions and must count the observable predictor's coefficients, including its initial state, not only local mechanism tables.
- Efficient residual checking requires an explicit bounded-width assumption on the actual doubled one-step contraction networks.
- The separately identified one-actuator control families and their full local spans are calibration information. This is not a solution to discovery from unconstrained raw trajectories with no supplied architecture.

## 1. Precise hypotheses

Let \(X=\prod_{i=1}^n[d_i]\), \(N=|X|\), and let the controlled instrument have nonnegative letter operators \(H_{u,y}\in\mathbb R^{N\times N}\), with column-stochastic totals

\[
 M_u=\sum_y H_{u,y}.
\]

Individual \(H_{u,y}\) are generally **substochastic**, not each stochastic. Otherwise their sum could not be stochastic for a nontrivial output alphabet.

Assume a no-actuation control with \(M_0=D\), where \(D\) is invertible. For each component \(i\), controls satisfy

\[
 M_{i,k}=D K_{i,k},
\]

where \(K_{i,k}\) acts only on coordinate \(i\). The linear span of the local matrices, including identity if supplied separately, is

\[
 \mathcal S_i=\{A\in\mathbb R^{d_i\times d_i}:\mathbf1_i^TA=\lambda\mathbf1_i^T
 \text{ for some }\lambda\in\mathbb R\}.
\]

The actual controls may be strictly positive and invertible stochastic matrices. Their **linear combinations** need not be positive or invertible. It is their real span, not their positive convex hull, that is used below.

Such a spanning family exists. The affine space of column-stochastic matrices has dimension \(d_i^2-d_i\). It contains strictly positive invertible points, for example \((1-\epsilon)I+\epsilon J\), where \(J\) is the uniform averaging matrix and \(0<\epsilon<1\). Sufficiently small independent zero-column-sum perturbations give an affine basis of strictly positive invertible stochastic matrices. Their linear span is \(\mathcal S_i\), of dimension \(d_i^2-d_i+1\). Identity can be supplied as the separate no-actuation choice; it is not strictly positive for \(d_i>1\).

All controlled words are allowed. Let \(\pi\ge0\), \(\mathbf1^T\pi=1\), and define

\[
 R=\operatorname{span}\{H_w\pi:w\text{ any controlled word}\},
 \qquad
 W=\operatorname{span}\{\mathbf1^TH_w:w\text{ any controlled word}\}.
\]

## 2. Full hidden reachability is valid

Both \(R\) and \(W\) are invariant under all letter operators, hence under every unconditional total. In particular

\[
 DR\subseteq R,\qquad WD\subseteq W.
\]

Because \(D\) is invertible and the spaces are finite-dimensional, these inclusions are equalities, so both spaces are also invariant under \(D^{-1}\). Therefore

\[
 K_{i,k}R=D^{-1}M_{i,k}R\subseteq R,
\qquad
 WK_{i,k}=WD^{-1}M_{i,k}\subseteq W.
\]

By linearity they are invariant under every embedded matrix of \(\mathcal S_i\). In particular, for every local state \(a\), the local reset map

\[
 E_{i,a}=e_a\mathbf1_i^T
\]

belongs to this span. Products of the coordinate reset maps send any probability vector to a specified global point state:

\[
 \left(\prod_i E_{i,x_i}\right)\pi=e_x.
\]

Thus all \(e_x\) lie in \(R\), proving \(R=\mathbb R^N\). There is no assumption that the resets are actual available positive controls; only linear invariance is being established.

Consequently the controlled Hankel rank is

\[
 r=\dim W.
\]

This avoids any hidden reachable-subquotient problem: the hypotheses have forced the reachable space to be the entire hidden state space.

## 3. The invariant-subspace classification is correct

Take a fixed splitting of each local row-function space

\[
 \mathbb R^{[d_i]}=L_i\oplus U_i,
 \qquad L_i=\operatorname{span}\{\mathbf1_i^T\},
\]

where \(U_i\) can be the zero-sum contrasts. For a subset \(S\subseteq[n]\), define

\[
 V_S=\bigotimes_{i\in S}U_i\otimes\bigotimes_{i\notin S}L_i.
\]

The row-function space is the direct sum of the \(V_S\). Coordinates with \(d_i=1\) can be removed, or their zero-dimensional interaction blocks ignored.

Three facts prove the claimed classification without a semisimplicity assumption:

1. **Block projectors are available.** The projector onto constants and its complementary contrast projector lie in \(\mathcal S_i\). Products of these local projectors give the projector onto each \(V_S\). Invariance therefore implies
   \(W=\bigoplus_S(W\cap V_S)\).
2. **Each block is irreducible for the diagonal local actions.** On \(U_i\), the corresponding diagonal block of \(\mathcal S_i\) can be any endomorphism. Tensor products of these endomorphisms span \(\operatorname{End}(V_S)\). Hence \(W\cap V_S\) is either zero or all of \(V_S\).
3. **Contrasts can be removed.** The parabolic algebra contains arbitrary maps \(U_i\to L_i\). Applying a nonzero such map to \(V_S\), for \(i\in S\), gives a nonzero part of \(V_{S\setminus\{i\}}\), hence that entire block must be present.

It follows that

\[
 W=\bigoplus_{S\in\mathcal I}V_S
\]

for a downward-closed family \(\mathcal I\) of subsets. Conversely every such direct sum is invariant under the local algebras. Since the empty word gives \(\mathbf1^T\in W\), the family contains the empty subset.

In particular

\[
 r=\sum_{S\in\mathcal I}\prod_{i\in S}(d_i-1).
\]

## 4. Quotient CP rank and its precise meaning

Choose fixed local bases of constants and contrasts. The preceding direct sum gives a basis \(g_1,\ldots,g_r\) of \(W\), each of which is a product function:

\[
 g_j(x)=\prod_i g_{j,i}(x_i).
\]

Let \(Z\in\mathbb R^{r\times N}\) have these functions as rows. Any quotient map \(F:\mathbb R^N\to\mathbb R^r\) realizing a minimal observable predictor has row space \(W\), so

\[
 F=CZ\quad\text{for some }C\in\mathrm{GL}_r.
\]

Viewed as an order-\((n+1)\) tensor with one observable-coordinate index and the \(n\) physical indices,

\[
 F_{a,x_1,\ldots,x_n}
 =\sum_{j=1}^r C_{aj}\prod_i g_{j,i}(x_i).
\]

Thus its **real signed** CP rank is at most \(r\). The observable-index-versus-physical-indices matrix flattening has rank \(r\), so the CP rank is in fact exactly \(r\).

Neither the contrasts nor the coefficients \(C_{aj}\) need be nonnegative. Calling this a nonnegative CP decomposition or treating its terms as positive hidden states would be incorrect.

## 5. Initial compression is valid, but not stationary compression

Since \(\mathbf1^T\in W\), there is a row \(\ell\) such that

\[
 \ell F=\mathbf1^T.
\]

All columns \(Fe_x\) lie in the affine hyperplane \(\ell z=1\). Their affine span has dimension \(r-1\), because \(F\) has rank \(r\). Moreover

\[
 F\pi\in\operatorname{conv}\{Fe_x:x\in X\}.
\]

Carathéodory therefore gives global point states \(x^{(1)},\ldots,x^{(s)}\), \(s\le r\), and weights \(p_j\ge0\), \(\sum_jp_j=1\), such that

\[
 F\pi=\sum_{j=1}^s p_jFe_{x^{(j)}}.
\]

The replacement

\[
 \pi'=\sum_jp_je_{x^{(j)}}
\]

is a mixture of at most \(r\) product point states. Every future row lies in \(W\), so this replacement preserves all controlled word probabilities.

It need not preserve \(D\pi=\pi\). For example, let \(n=1,d_1=2\), use an uninformative one-symbol sensor, and take

\[
 D=\begin{bmatrix}3/4&1/4\\1/4&3/4\end{bmatrix}.
\]

Add any locally spanning calibrated control family. Then \(r=1\), and the unique stationary hidden law is \((1/2,1/2)^T\). A single point state is observationally equivalent, but no point state is stationary. Therefore a certificate promising both this sparse point-mixture form and hidden stationarity would require a different argument and can fail in the proposed form.

## 6. When the bound becomes exponential or trivial

The theorem provides no bound forcing \(r\ll N\). If any observable row has a nonzero component in \(V_{[n]}\), the local algebra action fills that entire block, and downward closure then fills every block. Thus \(r=N\). A generic full-state emission probability has such a highest-order component.

There is an additional collapse in standard before-transition diagonal-emission models. If

\[
 H_{0,y}=D\operatorname{diag}(e_y),
\]

then \(WD^{-1}=W\) implies that \(W\) is invariant under multiplication by each emission function \(e_y\). If the linear span of the available emissions contains a nonconstant function of each individual coordinate, then these multiplications, combined with local \(\mathcal S_i\) actions, generate every product function. Therefore \(r=N\).

For the last claim, inductively multiply a function on already-generated coordinates by a nonconstant function of a new coordinate, subtract its constant part, and apply the full local endomorphism action to obtain every contrast on the new coordinate. Repeating this creates the entire product basis.

This does **not** mean every diagonal-emission model must have \(r=N\): structurally restricted or partly unobservable models can have smaller row spaces. But it means the compact regime is a substantive restriction, not a generic consequence of calibrated local actuation.

## 7. Exact verification and bit complexity

If a certificate supplies the hidden local circuit, the signed CP quotient \(F\), the observed predictor \(A_{u,y}\), output row \(\ell\), and compressed initial mixture, the core realization checks are

\[
 FH_{u,y}=A_{u,y}F,\qquad \ell F=\mathbf1^T,
 \qquad F\pi'=\alpha_{\rm obs},
\]

together with nonnegative/stochastic hidden mechanisms. These equalities imply equality of all word probabilities by induction. They are a sound verification route independent of how the certificate was found.

One can check an intertwining identity by contracting the exact squared Frobenius residual. Expanding the two CP copies produces polynomially many terms in \(r\), but the cost of each term is controlled by the width of the **actual doubled one-step tensor network**, including the identified physical indices. If that width and local dimensions are bounded, exact contraction is polynomial in the circuit size, \(r\), and rational input bit lengths. A single-copy width assertion should not silently substitute for this doubled-network hypothesis.

A polynomial count of real parameters is not automatically a polynomial binary certificate. Arbitrary \(\pi\) can encode arbitrary real observable data. A clean bit theorem should assume a rational target predictor (including \(\alpha_{\rm obs}\) and \(\ell\)) and rational local mechanism tables, and count both input bit lengths.

Under those rational assumptions the bit-size claim is supportable:

- Choose \(r\) independent future-test rows of the target predictor of word lengths at most \(r-1\). Their observable test matrix is rational and invertible.
- The matching hidden future-test rows are rational and span \(W\); multiplying by the inverse observable test matrix yields a rational quotient \(F\).
- Expressing its rows in the fixed rational product basis yields a rational \(r\times r\) coefficient matrix. Word lengths, local circuit sizes, and rational linear-algebra determinant bounds give polynomial bit lengths. Exponentially many hidden summands do not themselves force exponentially many bits: their number contributes logarithmically to numerator size.
- Carathéodory's support can be chosen as a basic feasible solution with at most \(r\) point states. Since \(F\) and \(\alpha_{\rm obs}\) are rational, its weights can be rational with polynomial determinant bounds.

This is a certificate-existence and checking statement, not an efficient algorithm for finding the unknown architecture, the downward ideal, or the point-state support. Likewise global invertibility of \(D\) is a theorem hypothesis; unless a separate efficiently checkable inverse/factorization promise is supplied, it should not be claimed to have been established merely by the local residual checks. The residual identities can establish the desired realization without separately rechecking every hypothesis used to guarantee that a compact witness exists.

## Recommended final formulation

State a restricted result for **rational, calibrated, locally span-rich controlled models** with invertible common drift, an exact minimal rational observed predictor of rank \(r\), and bounded doubled one-step contraction width. Then:

- a signed-CP-rank-\(r\) quotient witness exists;
- an observationally equivalent initial mixture of at most \(r\) product point states exists;
- these yield a polynomial-size, polynomially checkable exact realization certificate when all relevant input bit lengths are counted;
- no small-\(r\), hidden-stationarity, positive-CP, architecture-identifiability, or efficient-discovery conclusion is implied.
