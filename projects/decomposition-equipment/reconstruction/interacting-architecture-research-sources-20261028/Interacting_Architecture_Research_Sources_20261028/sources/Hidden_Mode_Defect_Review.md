# Independent audit: the observable hidden-mode defect bound

**Verdict.** The proposed bound is correct for a state-emitting hidden Markov realization in which the two channels are conditionally independent **at the same hidden state**, with a fixed transition before both emissions or after both emissions. It survives a nonminimal hidden realization and the reachable/observable subquotient. The stated before-transition factorization is correct exactly as written. It is false for unrestricted edge-emitting realizations, including channels conditionally independent given an edge, or for channels emitted at opposite ends of a transition.

**Interpretation.** This is a necessary hidden-state-count obstruction, not an architecture-discovery or positive-realization theorem. In fact it is exactly an ordinary split-channel matrix-flattening rank bound:

\[
 r+\operatorname{rank}F=\operatorname{rank}[E_{ab}]_{a,b}
 =\operatorname{rank}[T^{\rm obs}_{ab}]_{a,b}\le K.
\]

The last formulation does not require invertible observable total transition. There is an additional limitation: for an exact global minimal observable representation, if the *full hidden transition* is invertible, the defect is identically zero.

All assertions below are proved directly; no empirical rank calculation or unproved identification claim is used.

## 1. Exact assumptions and timing

Let the finite observation alphabets be \(\mathcal A,\mathcal B\), of sizes \(m,n\). Work over \(\mathbb R\), in the column-state convention. A hidden realization has:

- \(K\) hidden states;
- a nonnegative column-stochastic transition matrix \(P_h\in\mathbb R^{K\times K}\);
- diagonal nonnegative emission matrices \(D_a,D_b\), with
  \(\sum_aD_a=\sum_bD_b=I_K\);
- a probability initial column \(\pi\) and terminal row \(\mathbf1^T\).

The repeated letters \(D_a,D_b\) designate the two separate channel families. Conditional independence **given the same current hidden state** gives the hidden letter operator

\[
 L_{ab}=P_hD_aD_b.
\]

Thus the two observations are drawn at the departure state and the transition follows them. Diagonality implies that \(D_aD_b=D_bD_a\), but no commutation with \(P_h\) is assumed. Hidden invertibility, stationarity, irreducibility, strictly positive probabilities, full hidden reachability, and a minimal hidden realization are **not** assumptions of the bound.

For a chronological word \(w=s_1\cdots s_\ell\), set \(L_w=L_{s_\ell}\cdots L_{s_1}\), so \(p(w)=\mathbf1^TL_w\pi\). Let the rank of the full, infinite probability Hankel matrix be \(r\). This is the minimal real-linear observable dimension, not necessarily the minimal number of positive hidden states. The additional hypothesis for defining the proposed defect is invertibility of the total observable transition \(P_{\rm obs}\).

Exact probabilities and exact ranks are intended. Finite-data estimation, numerical rank thresholds, and statistical certification are separate problems.

## 2. Finite Hankel bases and the reachable/observable subquotient

Define the hidden reachable vector space and its unobservable subspace by

\[
 V=\operatorname{span}\{L_u\pi:u\text{ any word}\},
 \qquad
 N=\{x\in V:\mathbf1^TL_vx=0\text{ for every word }v\}.
\]

Both \(V\) and \(N\) are invariant under every \(L_{ab}\), hence under their sum \(P_h\). Standard linear algebra, or the definition of the Hankel map from reachable columns to all future probabilities, gives

\[
 \dim(V/N)=r.
\]

Choose \(r\) prefix words \(u_i\) and \(r\) suffix words \(v_j\) forming an invertible full-rank Hankel minor. Put

\[
 B_h=[L_{u_i}\pi]_i\in\mathbb R^{K\times r},\qquad
 O=[\mathbf1^TL_{v_j}]_j\in\mathbb R^{r\times K},\qquad H=OB_h.
\]

The matrix entries are \(H_{ji}=p(u_i v_j)\). Define \(Q=H^{-1}O\) and \(q=Q|_V\). Then \(qB_h=I_r\). Also \(N\subseteq\ker q\), and \(q\) has rank \(r\) on \(V\); dimension counting gives \(\ker q=N\). Consequently, for every \(x\in V\),

\[
 x-B_hqx\in N.
\]

Invariance of \(N\) under a letter operator therefore yields

\[
 qL_{ab}x=qL_{ab}B_hqx.
\]

The correct minimal observable matrices in these coordinates are

\[
 T^{\rm obs}_{ab}=QL_{ab}B_h
 =H^{-1}OP_hD_aD_bB_h,
 \qquad
 P_{\rm obs}=\sum_{a,b}T^{\rm obs}_{ab}=QP_hB_h.
\]

They genuinely represent the quotient dynamics, not merely a fitted one-step compression. With initial coordinate \(q\pi\) and terminal functional \(\mathbf1^TB_h\), they reproduce every word probability. This proves validity even when the hidden realization is nonminimal, \(V\ne\mathbb R^K\), and \(N\ne0\).

**The important danger:** in general neither \(D_a\) nor \(D_b\) is known to preserve \(V\) or \(N\). Therefore it is invalid to simply declare their restrictions to the observable quotient to be diagonal or commuting. The proof below never does so. It uses their ambient \(K\)-dimensional matrices and a rank-\(r\) projection that need not commute with them.

An arbitrary invertible sampled Hankel minor smaller than the full Hankel rank does not establish a minimal observable representation or a global closure theorem. Interestingly, the finite matrix factorization below still gives a rank bound for such a compression, if its compressed total transition is invertible; what fails is the global/minimal interpretation. From finite trajectories alone, determining that the selected minor reaches the full process rank requires further assumptions or evidence.

## 3. Factorization and rank proof

Assume \(P_{\rm obs}\) is invertible and define

\[
 A=P_{\rm obs}^{-1}QP_h\in\mathbb R^{r\times K},
 \qquad B=B_h\in\mathbb R^{K\times r}.
\]

By construction,

\[
 AB=P_{\rm obs}^{-1}QP_hB_h=I_r.
\]

This identity requires no inverse of \(P_h\). It implies that \(B\) is injective, \(A\) is surjective, and

\[
 R=I_K-BA
\]

is an idempotent with

\[
 R^2=R,\quad \ker R=\operatorname{im}B,\quad
 \operatorname{im}R=\ker A,\quad \operatorname{rank}R=K-r.
\]

Set

\[
 E_{ab}=P_{\rm obs}^{-1}T^{\rm obs}_{ab}=AD_aD_bB,
 \quad E_a=\sum_bE_{ab}=AD_aB,
 \quad E_b=\sum_aE_{ab}=AD_bB.
\]

The same-state channel normalization is used in both marginal identities. Thus

\[
 E_{ab}-E_aE_b
 =AD_a(I_K-BA)D_bB
 =AD_aRD_bB.
\]

For the \(mr\times nr\) block matrix \(F=[E_{ab}-E_aE_b]_{a,b}\), this gives

\[
 F=
 \begin{bmatrix}AD_{a_1}R\\ \vdots\\ AD_{a_m}R\end{bmatrix}
 \begin{bmatrix}RD_{b_1}B&\cdots&RD_{b_n}B\end{bmatrix}.
\]

The doubled \(R\) is legitimate because \(R^2=R\). Equivalently one may use \([AD_a]_aR[D_bB]_b\). In either form,

\[
 \operatorname{rank}F\le \operatorname{rank}R=K-r,
 \qquad \boxed{K\ge r+\operatorname{rank}F}.
\]

For the opposite marginal product, define a separate block matrix \(G_{ba}=E_{ab}-E_bE_a\), indexed by \((b,a)\). It factors as \([AD_b]_bR[D_aB]_a\) and obeys the same upper bound \(K-r\). One must exchange the block indices as well as the product order; blockwise transposition alone is not ordinary matrix transposition and need not preserve rank. The present review uses \(F_{ab}\) and the order \(E_aE_b\) throughout.

## 4. Gauge invariance and the flattening identity

Changing minimal observable basis by any \(S\in\mathrm{GL}_r\) gives

\[
 T'_{ab}=S^{-1}T_{ab}S,
 \quad P'=S^{-1}P_{\rm obs}S,
 \quad E'_{ab}=S^{-1}E_{ab}S.
\]

Consequently

\[
 F'=(I_m\otimes S^{-1})F(I_n\otimes S),
\]

so \(\operatorname{rank}F\) is invariant. This is also the relation between different full-rank Hankel prefix/suffix choices, since each gives coordinates on the same quotient \(V/N\). Reordering either alphabet only permutes block rows or columns and does not change the rank.

More decisively, let

\[
 C=[E_{ab}]_{a,b},\qquad
 U=\mathbf1_m^T\otimes I_r,\qquad
 W=\mathbf1_n\otimes I_r.
\]

Then \(CW=[E_a]_a\), \(UC=[E_b]_b\), and \(UCW=\sum_{a,b}E_{ab}=I_r\). Therefore

\[
 M=\begin{bmatrix}I_r&UC\\ CW&C\end{bmatrix}
 =\begin{bmatrix}U\\ I_{mr}\end{bmatrix}
 C\begin{bmatrix}W&I_{nr}\end{bmatrix}.
\]

Since \(C\) is a submatrix of \(M\), while the displayed factorization gives the reverse rank inequality, \(\operatorname{rank}M=\operatorname{rank}C\). Block Gaussian elimination at the \(I_r\) pivot gives

\[
 \operatorname{rank}M=r+\operatorname{rank}(C-CWUC)
 =r+\operatorname{rank}F.
\]

Also

\[
 C=(I_m\otimes P_{\rm obs}^{-1})[T^{\rm obs}_{ab}]_{a,b},
\]

and hence

\[
 \boxed{r+\operatorname{rank}F
 =\operatorname{rank}[E_{ab}]_{a,b}
 =\operatorname{rank}[T^{\rm obs}_{ab}]_{a,b}.}
\]

The direct hidden factorization of the unnormalized block matrix is

\[
 [T^{\rm obs}_{ab}]_{a,b}
 =\begin{bmatrix}QP_hD_{a_1}\\\vdots\\QP_hD_{a_m}\end{bmatrix}
   \begin{bmatrix}D_{b_1}B_h&\cdots&D_{b_n}B_h\end{bmatrix}.
\]

Thus \(K\ge\operatorname{rank}[T^{\rm obs}_{ab}]\) is immediate without assuming \(P_{\rm obs}\) invertible. Invertibility is needed only for the normalized defect interpretation and its expression as an increment over \(r\).

In raw Hankel terms, use the observable middle-letter entries

\[
 (H_{ab})_{ji}=p(u_i\,(a,b)\,v_j)= (OL_{ab}B_h)_{ji}.
\]

Since \(T^{\rm obs}_{ab}=H^{-1}H_{ab}\), the same lower bound equals the rank of \([H_{ab}]_{a,b}\). This is the ordinary matrix flattening whose row index is \((a,j)\) and column index is \((b,i)\). It is not a new independent tensor invariant hidden by the defect notation.

## 5. A significant limitation: invertible hidden transition forces zero defect

Suppose now, additionally, that \(P_h\) itself is invertible and that the selected Hankel basis has the full process rank \(r\). Because \(V\) and \(N\) are finite-dimensional and invariant under \(P_h\), injectivity of \(P_h\) implies

\[
 P_hV=V,\qquad P_hN=N.
\]

Both spaces are consequently invariant under \(P_h^{-1}\). Since

\[
 D_a=P_h^{-1}\sum_bL_{ab},\qquad
 D_b=P_h^{-1}\sum_aL_{ab},
\]

both channel families preserve \(V\) and \(N\). They therefore descend to linear maps \(\bar D_a,\bar D_b\) on \(V/N\), and their products descend as products. The quotient transition is invertible, and

\[
 T^{\rm obs}_{ab}=P_{\rm obs}\bar D_a\bar D_b,
 \qquad E_a=\bar D_a,\quad E_b=\bar D_b,
 \quad E_{ab}=\bar D_a\bar D_b.
\]

Hence \(F=0\). A nonzero exact defect rules out **every invertible hidden-transition realization of the specified same-state independent-channel form**, not just a realization with \(K=r\). The obstruction can be nontrivial for singular hidden transitions, such as latent refresh models. It should not be described as a generic signature of interacting latent dynamics.

This conclusion uses the full observable quotient. It need not hold for an arbitrary undersized finite compression.

## 6. Timing: both-after-transition is valid; mixed-time or edge emission is not

### Both channels after the transition

For the other standard state-emitting convention,

\[
 L_{ab}=D_aD_bP_h,
\]

the same observable total is \(QP_hB_h\). Set instead

\[
 \widetilde A=P_{\rm obs}^{-1}Q,
 \qquad \widetilde B=P_hB_h.
\]

Then \(\widetilde A\widetilde B=I_r\) and

\[
 E_{ab}=\widetilde A D_aD_b\widetilde B.
\]

The entire rank proof applies with these substituted factors. Thus the numerical bound is unchanged, but reusing the original \(A,B\) without accounting for timing would be incorrect. More generally, the proof applies to \(L_{ab}=L D_aD_b R_0\) with fixed surrounding factors and \(\sum L_{ab}=LR_0\), provided the middle dimension is \(K\) and the compressed total is invertible.

### Explicit edge/mixed-time counterexample

Let

\[
 K=2,\qquad
 P_h=\begin{bmatrix}3/4&1/4\\1/4&3/4\end{bmatrix},
 \qquad \pi=\tfrac12\begin{bmatrix}1\\1\end{bmatrix},
 \qquad D_0=\operatorname{diag}(1,0),\quad D_1=\operatorname{diag}(0,1).
\]

At each transition, emit \(a\) equal to the departure state and \(b\) equal to the arrival state. The two channels are deterministic, hence conditionally independent given the transition edge. The operators are

\[
 L_{ab}=D_bP_hD_a.
\]

Their sum is \(P_h\), and they are nonnegative. Reachability is full: for example, \(L_{00}\pi\) and \(L_{11}\pi\) are nonzero multiples of the two coordinate columns. Observability is full: the probabilities of the next departure label recover each hidden coordinate, since \(\sum_b\mathbf1^TL_{ab}=\mathbf1^TD_a\). Thus the observable rank is exactly \(r=2\). We may use the original hidden coordinates as an equivalent minimal observable basis, so \(P_{\rm obs}=P_h\), which is invertible.

We have

\[
 E_{ab}=P_h^{-1}D_bP_hD_a,\qquad
 E_a=D_a,\qquad E_b=P_h^{-1}D_bP_h.
\]

A direct rational calculation gives

\[
 P_h^{-1}=\begin{bmatrix}3/2&-1/2\\-1/2&3/2\end{bmatrix},
 \qquad
 P_h^{-1}D_0P_h=
 \begin{bmatrix}9/8&3/8\\-3/8&-1/8\end{bmatrix}.
\]

Consequently

\[
 F_{00}=P_h^{-1}D_0P_hD_0-D_0P_h^{-1}D_0P_h
 =M=\begin{bmatrix}0&-3/8\\-3/8&0\end{bmatrix},
\]

and normalization gives

\[
 F=\begin{bmatrix}M&-M\\-M&M\end{bmatrix},
 \qquad\operatorname{rank}F=\operatorname{rank}M=2.
\]

The putative extension to edge emissions would demand \(2=K\ge r+\operatorname{rank}F=4\), a contradiction. This failure is not due to correlated emissions conditioned on an edge: the edge-conditioned channels in this example are independent. It is the failure of a shared *state-level* diagonal product around a common transition.

For unrestricted edge-emitting models an even simpler example has one hidden state and a correlated binary output pair, but the two-state construction above establishes failure under the stronger edge-conditional-independence assumption.

## 7. What this certificate does and does not establish

The valid conclusion is:

> For a process with exact observable matrices, any positive hidden Markov realization with conditionally independent two-channel emissions at one shared hidden state must have at least \(\operatorname{rank}[T^{\rm obs}_{ab}]\) hidden states. When its observable total transition is invertible, this equals \(r+\operatorname{rank}F\).

It does **not** establish that:

- a realization attaining the lower bound exists;
- the relevant real-linear factors are nonnegative or stochastic;
- hidden components, their types, or their interaction wiring are identified;
- a positive local mechanism or compatible positive joint realization exists;
- a hidden model with edge or mixed-time emission obeys the bound;
- a finite empirical Hankel rank is the exact process rank;
- a vanishing defect suffices for positive realization or architecture discovery.

The shared-state emission model is an explicit modeling hypothesis. If the intended task is to infer typed positive interacting components from raw trajectories with no supplied latent architecture, this result can be used only as a scoped necessary test of one candidate realization class. It cannot be promoted to the main discovery theorem, and the flattening identity plus the invertible-hidden-transition limitation should be disclosed.
