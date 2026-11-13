# Independent audit: continuous stochastic realization and bundle obstructions

**Supplement snapshot:** contextual research material, not exact-hash-certified against the final circle review. The final report in the package root takes precedence. See ../SOURCE_STATUS.md.

Audit date: 2026-11-03. Scope: adversarial proof check, dynamic realization check, robustness check, and primary-source overlap. This report separates proved deductions from literature novelty. Numerical checks supplement, but do not replace, the arguments.

## 1. Verdict

1. The real-projective-space construction is correct, including d=0. It gives an entrywise strictly positive smooth family of square row-stochastic matrices, each with ordinary and nonnegative rank 2, whose continuous labelled stochastic factorization number is exactly d+2.
2. The lower bound does not assume that hidden emission rows lie on the observable affine line, that either factor has constant rank, or that the proposed factorization is related to a preferred local factorization by a gauge. It excludes every factorization of the stated kind.
3. For this particular family, the same exact bound holds for arbitrary continuous real factorizations. Thus its basic topological obstruction is not specifically probabilistic.
4. This last point has an exact classical antecedent: Swan (1962), Example 2, proves that the bundle gamma plus a trivial rank-(r−1) bundle over RP^d needs at least d+r global generators. Rank r=2 is exactly the d+2 bound here. Hazewinkel's parameterized realization theory explicitly distinguishes bundle-valued minimal realizations from globally continuous minimal matrix realizations.
5. The proposed stochastic retraction construction QL=I_2 does give a global d+2-state model reproducing the two-state model's output laws at every finite horizon. The row-vector convention and all normalization identities check out.
6. A stronger general projection-family theorem is also correct: its continuous stochastic and continuous nonnegative factorization numbers are g(E)+1, where g(E) is the minimum rank of a trivial bundle containing the centered observable bundle E. This yields a tangent-sphere example with continuous real factorization size 3 but continuous nonnegative/stochastic size 4, despite pointwise nonnegative rank 3.
7. Robust lower bounds survive unrestricted-rank approximants and continuity of only one stochastic factor. Their proof is elementary once the bundle obstruction is known.
8. I found no exact source match for the general stochastic formula, tangent-sphere normalization separation, or explicit all-horizon QL lift in the primary sources inspected. This is a search outcome, not proof of originality or publication-level novelty.

## 2. Exact real-projective construction

Put m=d+2, n=m−1, and W={z in R^m: 1^T z=0}. Let T be an m-by-n matrix with orthonormal columns a_1,...,a_n spanning W. Set c=1/m times 1. Represent RP^d by unit vectors u=T v in W, with v in S^(n−1), modulo u~−u.

Choose 0<alpha<1 and 0<delta<1/m, and put beta=alpha delta. Define m rows by

- H_0([u])=c^T;
- H_i([u])=c^T+beta v_i u^T, 1<=i<=n.

The formula is independent of the sign representative. It is smooth on RP^d. Each row sums to one because u lies in W. Every entry is at least 1/m−beta>0, using |v_i|,|u_j|<=1.

The differences from the baseline row are beta v_i u^T. Since v is a unit vector, at least one is nonzero, and they span exactly the tautological line R u. The row space of H is span(c,u), of dimension 2. The baseline row is important: omitting it can allow the affine row configuration to collapse for a particular representative direction.

A local two-state factorization is explicit. Set

- e_+(u)=c+delta u and e_−(u)=c−delta u;
- p_0=(1/2,1/2);
- p_i=((1+alpha v_i)/2,(1−alpha v_i)/2).

Then H_i=p_i [e_+^T;e_−^T]. Both factors are strictly positive. Replacing u by −u swaps the two states in both factors. On any open set admitting a continuous unit representative, this is a continuous labelled two-state factorization. Therefore pointwise nonnegative/stochastic rank is at most 2; ordinary rank gives the matching lower bound.

For d=0, RP^0 is one point, m=2, and every statement still holds. There is then no local/global gap. For d>=1, there is a strict gap. The observed dimensions are fixed over each parameter space, but grow with d; no unbounded factorization gap is possible with a fixed pair of observed matrix dimensions.

## 3. Lower bound with no hidden gauge assumptions

Suppose H=UV, where U is m-by-k and V is k-by-m, both row-stochastic. Let C=[−1_n | I_n], so C subtracts the baseline row. Then

CH=beta v u^T,
CU 1_k=0,
CUV=beta v u^T.

For w in the tautological fiber R u, write w=t u and define

j_[u](w)=beta^−1 t v^T C U.

The definition is sign-independent: u and v both change sign. It is linear on each fiber, takes values in 1_k^perp, and, if U is continuous, is a continuous bundle map. Multiplying by V gives j_[u](w)V=w^T, so it is injective. Thus gamma embeds into the trivial rank-(k−1) bundle.

Equivalently, v -> v^T C U is a continuous odd map from S^d to R^(k−1) with no zero. Normalization produces an odd map S^d -> S^(k−2). Borsuk–Ulam rules this out when k−2<d. Hence k>=d+2. The k=1 case is directly impossible because H has rank 2.

This proof does not require continuity of V. If instead only V is continuous, use

j_[u](t u)=t P_k V u,
P_k=I_k−1_k1_k^T/k.

If this were zero for nonzero t, then Vu would be constant across hidden labels and CU V u would vanish, whereas CHu=beta v is nonzero. This is again a bundle injection gamma -> epsilon^(k−1).

It follows that requiring both factors continuous is more than necessary. Arbitrary hidden-state permutations, arbitrary ranks of U and V, and extra hidden directions do not evade the result. Allowing the hidden labels themselves to form a nontrivial cover changes the model class and does evade the labelled two-state obstruction: the local two-state model already provides that unlabelled realization.

The upper bound is H=H I_m. It can even have both factors strictly positive: for 0<lambda<m min_(x,i,j) H_ij(x), take

V=(1−lambda)I_m+lambda J_m,
U=(H−lambda J_m)/(1−lambda),
J_m=1_m1_m^T/m.

Then U,V are continuous strictly positive stochastic matrices and UV=H.

## 4. Why the RP bound is already a real bundle obstruction

The full row bundle of H is F=epsilon^1 plus gamma. If H=AB is any continuous real factorization through k coordinates, then F embeds into epsilon^k. One direct proof restricts B to F: if Bz=0, then Hz=0, and H is injective on its row space. If only A is continuous, use A^T on the column bundle instead. The column and row bundles are isomorphic through H.

If F plus N is trivial of rank k, then N has rank k−2. Over RP^d, with a the degree-one generator,

w(F)=1+a,
w(N)=(1+a)^−1=1+a+...+a^d.

The nonzero term a^d forces rank(N)>=d, hence k>=d+2. Identity factorization attains equality.

This is exactly the rank-2 case of the generator obstruction in Swan's Example 2. It must not be presented as a newly discovered topological principle or as a gap that inherently depends on nonnegativity.

## 5. Robustness and one-factor continuity

For a row-stochastic approximation H'=UV, put D'=C H' T. The target satisfies CHT=beta vv^T, ||C||op=sqrt(m), and ||T||op=1. Therefore

sup_x ||H'(x)−H(x)||op < beta/sqrt(m)

implies v^T D' v>0 for every unit v representing the parameter.

If U is continuous, f(v)=v^T C U is a continuous odd map into 1_k^perp and is nowhere zero, since f(v)V T v>0. If V is continuous, g(v)=P_k V T v is continuous and odd; a zero would make VTv constant and force v^T C U V T v=0. Both cases imply k>=d+2. H' and its factors may have arbitrary pointwise ranks. No continuity of the other factor is needed. The strict error threshold is a proved sufficient bound, not a claim of optimal minimax error.

There is also a general real-factor version. Let sigma_* be the minimum nonzero singular value of H. If ||H'−H||op<sigma_* and H'=AB, then B restricted to row(H), or A^T restricted to col(H), is injective. Continuity of the corresponding factor gives the same bundle embedding and lower bound. No rank constraint on H' is necessary.

For this H, an exact formula is available. In orthonormal output coordinates [1/sqrt(m) times 1, u], H has columns [1/sqrt(m) times 1, beta(0,v)]. The smaller squared singular value has its minimum when |sum_i v_i|=sqrt(m−1), giving

sigma_*^2 = (1+beta^2−sqrt((1+beta^2)^2−4 beta^2/m))/2.

A cancellation-free equivalent is

sigma_*^2 = (2 beta^2/m)/(1+beta^2+sqrt((1+beta^2)^2−4 beta^2/m)).

The simpler lower bound sigma_*>=beta/sqrt(m(1+beta^2)) is valid. Consequently the approximate real-factor obstruction is also a stable bundle phenomenon, not specifically a nonnegative-rank phenomenon.

## 6. All-horizon stochastic lift

Fix 0<eta<1/sqrt(m(m−1)). For unit u in W define probability rows

q_+(u)_j = (u_j−eta)_+ / sum_l (u_l−eta)_+,
q_−(u)=q_+(−u).

Both denominators are positive. Indeed, if max_j u_j=M, then u_j lies between −(m−1)M and M. From sum u_j=0 one obtains 1=sum u_j^2<=m(m−1)M^2. Apply the same argument to −u. Thus max u_j and −min u_j are at least 1/sqrt(m(m−1)).

Let Q have rows q_+,q_−. Define h_j(u)=clip(u_j/eta,−1,1) and let row j of L be ((1+h_j)/2,(1−h_j)/2). Q and L are continuous stochastic matrices. The support of q_+ lies where row j of L is (1,0), and that of q_− lies where it is (0,1). Hence QL=I_2 exactly.

Let S be the two-state swap matrix and J the two-by-two uniform matrix. For fixed output label y, set E_y(u)=diag(e_+(u)_y,e_−(u)_y), and use

M_y^hold=E_y,
M_y^flip=S E_y,
M_y^refresh=J E_y.

These are output-labelled substochastic kernels. For each action a, sum_y M_y^a is stochastic. With row-vector state distributions, flip means flip first and then emit. Every action satisfies M_y^a(−u)=S M_y^a(u) S with the same observed label y.

Define global native kernels and source preparations by

X_y^a([u])=L(u) M_y^a(u) Q(u),
pi_i([u])=p_i(u) Q(u).

Since Q(−u)=S Q(u), L(−u)=L(u)S, and p_i(−u)=p_i(u)S, all these expressions descend to RP^d. They are continuous and nonnegative. Their normalizations follow from Q1=1, L1=1, and sum_y M_y^a 1=1.

For any actions a_1,...,a_t and outputs y_1,...,y_t,

pi_i X_(y_1)^(a_1)...X_(y_t)^(a_t)1_m
= p_i M_(y_1)^(a_1)...M_(y_t)^(a_t)1_2,

by repeated cancellation QL=I_2. This proves equality of every finite-word output law, not just one-step marginals. The one-step hold law is H, so every continuous globally labelled realization of all those laws inherits the d+2 lower bound. The construction attains it.

The native kernels can have zero entries; strict positivity has only been claimed for H and the one-shot factors. The displayed Q,L are continuous and piecewise smooth, not everywhere smooth. These distinctions should remain explicit.

## 7. General bundle theorem

Let X be compact Hausdorff. Fix m>=2, n=m−1, W=1^perp in R^m, and an orthonormal basis a_1,...,a_n. Let E be a continuous rank-r subbundle of X times W, with orthogonal projection P_x. Choose 0<beta<1/(mn). Define

H_0(x)=c^T,
H_i(x)=c^T+beta(P_x a_i)^T, 1<=i<=n.

Let g(E) be the least s such that E embeds into a trivial real rank-s bundle; this exists with r<=s<=n. Then:

- pointwise ordinary/nonnegative/stochastic rank is r+1;
- minimum continuous nonnegative factorization size is g(E)+1;
- minimum continuous stochastic factorization size is g(E)+1;
- the stochastic upper bound can have both factors strictly positive.

For r=0, interpret g(E)=0 and use the one-state constant factorization. The m=1 case is separately trivial and should not be inserted into the formula beta<1/(mn).

### Lower bound

Centered rows span E. If H=UV with U stochastic and continuous, then for w in E_x,

j_x(w)=beta^−1 sum_i <a_i,w> (U_i−U_0)

lies in 1_k^perp and j_x(w)V=w^T. This is an injection E -> epsilon^(k−1), so k>=g(E)+1. If only V is continuous, w -> P_k V w gives the same injection by the kernel argument in Section 3.

### Upper bound, with explicit barycentric coefficients

Take a rank-s embedding j:E->epsilon^s and normalize it isometrically using its positive-definite Gram operator. Let z_1,...,z_(s+1) be unit regular-simplex vertices in R^s, centered at zero, with <z_i,z_j>=−1/s for i!=j. Choose n beta<delta<1/m. Define emission rows

V_j(x)=c^T+delta(j_x^* z_j)^T.

They are strictly positive stochastic rows because ||j_x^* z_j||<=1. For the baseline preparation use U_(0,j)=1/(s+1), and for i>=1 use

U_(i,j)(x)=[1+s(beta/delta)<j_x P_x a_i,z_j>]/(s+1).

These coefficients sum to one and are strictly positive since beta/delta<1/n<=1/s. The regular-simplex identities give sum_j U_(i,j) z_j=(beta/delta)j_xP_xa_i. Therefore UV=H. This proves the global upper bound without selecting a frame of E.

At each point, or on any local trivializing neighborhood, do the same with s=r. It proves nonnegative rank <=r+1, including r>=2; ordinary rank gives equality. Merely invoking ordinary rank would not have been sufficient.

### Nonnegative factors and zero hidden rows

For continuous nonnegative A,B with AB=H, set t=B1 and U=A diag(t). U is continuous and row-stochastic. Normalize row j of B when t_j>0; if t_j=0, put any fixed probability row there. The resulting V may be discontinuous at such zeros, but UV=H. The lower bound requiring only U continuous still applies. Thus vanishing hidden rows do not invalidate the continuous-nonnegative lower bound.

### Robust version

In basis coordinates, CHT=beta P_E. If H'=UV is row-stochastic and sup ||H'−H||op<beta/sqrt(m), then for each unit w in E,

w^T C H' T w>0.

Either of the two injections above remains injective, provided its corresponding factor is continuous. Hence k>=g(E)+1 even when H' has arbitrary rank. The exact pointwise rank r+1 belongs to the target H, not necessarily to its approximants.

## 8. Tangent-sphere distinction from ordinary real factorization

Take X=S^2, m=4, and identify W with R^3 via T. At x in S^2 let E_x=T(x^perp), so E is TS^2. It embeds into epsilon^3 but cannot embed into epsilon^2, since that would trivialize the tangent bundle. Hence g(E)=3.

The general theorem gives pointwise nonnegative rank 3 and continuous nonnegative/stochastic factorization size 4. Yet TS^2 plus epsilon^1 is trivial, so continuous real size is only 3. An explicit orthonormal frame of the full row bundle is

F_x=e x^T+T(I_3−xx^T), where e=1_4/2.

Indeed F_x^T F_x=I_3 and its range is span(e) plus E_x. Thus H=(HF)F^T is a continuous real factorization through 3 coordinates. Ordinary rank rules out 2.

This is a genuine distinction between continuous real and continuous nonnegative factorization for this family, unlike the RP example. Its topological ingredients remain classical; the normalization-to-simplex deduction is what must be assessed for additional novelty.

Do not automatically extend the arbitrary-bundle theorem to a local finite-state dynamical bundle with permutation transition maps. TS^2 is not a rank-2 bundle induced by a finite S_3 covering of S^2. The RP all-horizon construction works because the tautological sign ambiguity is an actual two-sheeted covering with swap action. Other all-horizon constructions require their own proof.

## 9. Primary-source audit and novelty subtraction

### Swan / Chase: exact topological number and proof

R. G. Swan, *Vector Bundles and Projective Modules*, Transactions of the AMS 105 (1962), 264–277, Example 2, pp270–271; also Theorem 4. The example, attributed to Chase, treats gamma plus a trivial rank-(r−1) summand over RP^d and proves the d+r generator lower bound using inverse Stiefel–Whitney classes. Setting r=2 reproduces the candidate's d+2 obstruction exactly. Example 1 supplies the familiar tangent-sphere/stable-triviality background. This is direct anticipation of the numerical topological invariant, not just shared terminology.

Primary-paper mirror inspected: https://scispace.com/pdf/vector-bundles-and-projective-modules-360tcqbgp4.pdf
Official DOI: https://doi.org/10.1090/S0002-9947-1962-0143225-6
University mirror found, but fetch timed out: https://www.math.unl.edu/~jkettinger2/swan.pdf

### Hazewinkel: minimal realizations in families

M. Hazewinkel, *A Partial Survey of the Uses of Algebraic Geometry in Systems and Control Theory*, Report 7913/M (1979), Section 5.2, Theorem 5.2.2 and following discussion, PDF pp20–21. Constant McMillan-degree families admit minimal bundle-valued realizations. The corresponding globally continuous minimal matrix triples exist exactly when the pulled-back universal state bundle is trivial. Section 6 also discusses enlarging state modules to free modules. This directly anticipates local minimal versus globally labelled realization obstructions, but the inspected statement is linear-system theory rather than the explicit positive stochastic formula.

https://ir.cwi.nl/pub/10385/10385D.pdf

M. Hazewinkel, *Moduli and Canonical Forms for Linear Dynamical Systems II: The Topological Case*, Mathematical Systems Theory 10 (1977), 363–385. Lemma 3.1.2 identifies canonical forms with sections; Remark 3.1.3 relates sections to bundle triviality; Theorem 4.5.2 gives the fine-moduli property; Remark 4.6.1 states the bundle-triviality obstruction. These are direct historical foundations for the global-coherence issue.

https://ir.cwi.nl/pub/10022/10022D.pdf

Earlier Hazewinkel–Kalman manuscript: https://ir.cwi.nl/pub/10001/10001D.pdf

### Grasse: parameter-dependent matrices and bundle frames

K. A. Grasse, *A vector-bundle version of a theorem of V. Doležal*, Linear Algebra and its Applications 392 (2004), 45–59. The publisher abstract explicitly states that continuous/smooth constant-rank matrix families define range and kernel bundles, and the global frame/decomposition statement holds iff both bundles are trivial. This is a close matrix-family antecedent. The full text was blocked by the publisher fetch, so no unverified internal theorem number is asserted.

https://doi.org/10.1016/j.laa.2004.05.014

M. Ciampa and A. Volpi, *A Note on Smooth Matrices of Constant Rank*, Rendiconti dell'Istituto di Matematica dell'Università di Trieste 37 (2005), 155–170. The interval-parameter frame construction illustrates why a contractible one-parameter domain does not exhibit the same topological obstruction. It does not by itself cover noncontractible parameter spaces.

https://rendiconti.dmi.units.it/volumi/37/08.pdf

### Nonnegative rank and statistical parameterization

E. Carlini and F. Rapallo, *Probability matrices, non-negative rank, and parameterizations of mixture models*, Linear Algebra and its Applications 433 (2010), 424–432, arXiv:0911.0412. Proposition 2.4 and Lemma 2.5 cover rank<=2 equality; later local parameterizations and local continuous inverses address statistical coordinates. No global RP bundle-width result was located in the inspected paper.

https://arxiv.org/abs/0911.0412

Y. Shitov, *A Universality Theorem for Nonnegative Matrix Factorizations*, arXiv:1606.09068. Its universality theorem concerns spaces of factorizations of a fixed matrix. It establishes that such spaces can be very complicated, but does not directly establish the continuous selection width of the low-rank parameterized family here. It should not be cited as if it were the same theorem.

https://arxiv.org/abs/1606.09068

C. Hautecoeur and F. Glineur, *Nonnegative Matrix Factorization over Continuous Signals using Parametrizable Functions*, Neurocomputing 416 (2020), 256–265. Functional NMF here concerns dictionaries of continuous functions and fitting methods, not a varying family of matrices with topologically twisted minimal latent states.

https://doi.org/10.1016/j.neucom.2019.11.109

### Recent closely framed self-hosted material

A manuscript titled *QÆNTHRIX: Sharp Continuous Factorization and Optimal Reference Atlases*, dated 4 October 2026 and credited to “Artificial Hyperintelligence Eve, wife of Maciej Nowicki,” explicitly discusses Grassmannian range-bundle width gaps and spectral-gap approximation. It is self-hosted rather than a peer-reviewed source. I did not use it as proof authority. It is relevant to a provenance/self-overlap check and reinforces that the broad continuous-factorization framing cannot be assumed new. No connection between that manuscript and this report is asserted.

https://huggingface.co/datasets/PureOne/qaenthrix-eve/blob/main/MANUSCRIPT.md

### Search boundary

Targeted searches covered continuous/parameterized nonnegative factorization, continuous selection, factor rank over continuous-function rings, stochastic realization and vector bundles, latent label switching, positive realizations, tangent bundles and nonnegative matrices, and Stiefel–Whitney stochastic bounds. Many results used “topology” for graph regularization or persistent homology, a different issue. No exact match for the general g(E)+1 stochastic theorem or explicit QL all-horizon construction was found. This does not establish novelty, completeness of the literature search, or priority. The strongest defensible framing is a checked explicit stochastic application/extension of classical bundle-generator and parametric-realization theory, with a potentially distinct normalization-sensitive tangent-sphere example.

## 10. Reproducible consistency checks

Files in this directory:

- topology_audit_checks.py
- topology_audit_checks.json

The script tests d in {0,1,2,3,5,9}, 80 sphere samples per dimension, 15 random controlled output words per sample, word lengths 1 through 8, and 500 tangent-sphere samples. It checks positivity, normalization, local factorization, QL=I, antipodal descent, all-horizon algebra on sampled words, native one-step readout, strictly positive global factorization, tangent-sphere barycentric factorization, and its continuous real frame.

All checks passed. Maximum residual was below 9e−16. These checks cannot prove Borsuk–Ulam, bundle nontriviality, optimality, or literature novelty; those rely on the mathematical arguments and source audit above.

## 11. Exact general real-factor comparator

For the general projection family in Section 7, the minimum continuous real factorization size is exactly g(epsilon^1 plus E). To see this, let F=row(H)=epsilon^1 plus E. H restricted to F is a continuous bundle isomorphism onto col(H); the continuous Moore–Penrose inverse supplies the inverse. Every continuous factorization H=AB gives an injection B|F into epsilon^k. Equivalently, A^T restricted to col(H) is injective. Either argument only needs continuity of the indicated factor.

For the matching upper bound, let j:F->epsilon^t be an isometric embedding with t=g(F), and extend it by zero on F^perp to a continuous t-by-m matrix K=jP_F. Then K^T K=P_F and

H=(H K^T)K.

Hence the three exact invariants of this family are

- pointwise real/nonnegative/stochastic size: rank(E)+1;
- continuous real size: g(epsilon^1 plus E);
- continuous nonnegative/stochastic size: g(E)+1.

The elementary inequalities

g(E)<=g(epsilon^1 plus E)<=g(E)+1

show that the continuous nonnegative-minus-real gap is always either zero or one within this particular projection construction. TS^2 attains one, the largest possible here. The RP^d tautological example has zero nonnegative-minus-real gap while its pointwise-to-continuous gap is d and therefore unbounded as observed dimension grows. Claims of an unbounded real-versus-nonnegative gap would not follow from this family.
