# Independent audit: a Moore-space family with widths 3, 4, and 5

## Verdict

The proposed example works. For X = S^1 union_degree_3 D^2 = M(Z/3,1), take the principal S3 frame cover with monodromy sending the generator of pi1(X)=C3 to a 3-cycle. There is a four-output continuous family of uniform, persistent mixtures of three distinct strictly positive IID laws with this component cover. Its pointwise real/stochastic width is 3; its global normalized signed width is 4; its global stochastic width is 5. Its unconstrained real width, with varying terminal vector, is 3.

The supplied Double_Cover_Realization.tex proves only the split-interface criterion in rank >=3. The finite-block classifier argument below supplies the missing necessity for arbitrary stochastic native competitors in this persistent-IID setting. It does not assume a comparison map, minimality, reachability, stationarity of hidden states, constant recurrent-class structure, or continuity of limiting hidden-state distributions.

## 1. Native stochastic realizations force disjoint-support configurations

Let X be compact, Y finite with m symbols, and let a continuous unordered family have p distinct atoms v_i(x) and positive weights w_i(x). The labels live on its principal S_p frame cover P. Suppose a continuous globally labelled k-state native stochastic realization (rho,N_y) reproduces the all-word law

    f_x(w) = sum_i w_i(x) product_{letters y in w} v_i(x)_y.

Set d = min_{x,i!=j} ||v_i(x)-v_j(x)||_infty > 0 and a = min_{x,i} w_i(x) > 0. Fix epsilon = a/10. Choose an integer n > 9m/(epsilon d^2).

For a length-n word u, let hat v(u) be its empirical output frequencies. Choose a continuous h:[0,infinity)->[0,1] which is 1 on [0,d/6] and 0 on [d/3,infinity). Define

    chi_i(p,u) = h(||hat v(u)-v_i(p)||_infty),
    phi_i(p,u) = chi_i(p,u) + (1-sum_j chi_j(p,u))/p.

At most one chi_i is nonzero, since distinct centers are separated by d. Thus each phi_i is nonnegative, the phi_i sum to 1, and they depend continuously and equivariantly on the frame. Under IID atom j, the empirical frequency vector lies within d/6 of v_j with probability at least 1-epsilon: each coordinate has variance <=1/(4n), so Chebyshev and a union bound give failure probability <=9m/(nd^2). On that good event, phi_j=1 and all other phi_i=0.

Write c_ij = E_{v_j^n}[phi_i]. Then c_ii >= 1-epsilon and c_ij <= epsilon for i!=j. Pull the native model back from X to P and set

    A_i(p) = sum_{u in Y^n} phi_i(p,u) rho(x) N_u(x),
    B_{s i}(p) = sum_{v in Y^n} phi_i(p,v) (N_v(x) 1_k)_s.

B is a continuous k-by-p row-stochastic matrix. A_i is nonnegative. The exact target law on two consecutive blocks, and conditional independence of those blocks given the held atom, give

    A_i 1_k = sum_j w_j c_ij <= w_i + epsilon,
    (AB)_ii = sum_j w_j c_ij^2 >= w_i(1-epsilon)^2.

A_i1 is positive. Normalize Q_i=A_i/(A_i1). Since epsilon<=0.1 and epsilon/w_i<=0.1,

    (QB)_ii >= (1-epsilon)^2/(1+epsilon/w_i) >= 0.81/1.1 > 1/2.

Consequently every column i of B has some entry strictly greater than 1/2. Define

    R_{i s} = (B_{s i}-1/2)_+ / sum_t (B_{t i}-1/2)_+.

These denominators are positive. R is continuous, equivariant, and row-stochastic. No slot s can belong to two different row supports because the row B_s has total mass 1. Therefore R:P->D_{p,k}=Hom(K_p,K_k) is an equivariant map.

Conversely, the buffered decoder theorem in the supplied report turns any such map into a continuous equivariant stochastic split pair (Q,L) with QL=I_p. Then rho=wQ and N_y=L diag(v_{iy})Q descend to X and reproduce every word by telescoping. Thus, for compact separated persistent finite IID mixtures, the arbitrary-native stochastic width equals the least k admitting an equivariant map P->D_{p,k}.

This is an existence-level extraction. It does not show that the original native realization itself is conjugate to a split realization or that its hidden states have continuous ergodic decompositions.

## 2. A finite-horizon robustness consequence

The same argument uses only words of lengths n and 2n. If a native stochastic competitor approximates each such target word probability with error at most eta, then its corresponding A_i1 and (AB)_ii differ from the target values by at most m^n eta and m^(2n) eta, respectively. For the target,

    (AB)_ii - (A_i1)/2 >= a/4.

Indeed the lower bound is w_i((1-epsilon)^2-1/2)-epsilon/2; with epsilon=a/10<=0.1 it is at least 0.26a. Therefore

    eta (m^(2n) + m^n/2) < a/4

still forces (AB)_ii>(A_i1)/2 and the same D_{p,k} map. This gives a uniform finite-horizon positive gap whenever that map is topologically forbidden, without any bound on competitor parameters. The horizon/constant is deliberately crude.

## 3. D_{3,4}/S3 is exactly K4

The maximal cell dimension of D_{3,4} is 1. A vertex assigns the three labelled components to three distinct slots; there are 4*3*2=24 vertices. Its S3 orbit is determined exactly by the remaining vacant slot, hence there are four quotient vertices.

An edge lets one component move between two slots while the other two occupy the remaining slots. There are 3*binomial(4,2)*2=36 edges. After forgetting component labels, it is determined exactly by the two possible vacant slots at its endpoints. Consequently there is one edge between each unordered pair of the four quotient vertices and no loops: D_{3,4}/S3 is the graph K4.

The S3 action is free: a nonidentity row permutation cannot fix a tuple of nonempty pairwise disjoint row supports. It has no edge inversions, since a slot-vacancy change cannot arise by relabelling rows. Thus D_{3,4}->K4 is a principal S3 covering.

D_{3,4} is connected. Regard a vertex as a permutation of the three labels plus a vacancy; an edge swaps the vacancy with one label. Those three transpositions generate S4. In particular D_{3,4} has first Betti number 36-24+1=13, not 12.

If an S3-equivariant map F:P->D_{3,4} existed, its quotient f:X->K4 would exhibit P as the pullback of this covering. The monodromy representation would factor as

    pi1(X)=C3 -> pi1(K4)=F3 -> S3.

Every homomorphism from finite C3 to torsion-free free F3 is trivial, contradicting the specified nontrivial 3-cycle monodromy. Hence width 4 is impossible. Widths <=3 are also impossible because a map into D_{3,k} for k<=4 would compose with the slot inclusion into D_{3,4}.

## 4. D_{3,5} is simply connected: an elementary proof

Let A_i be the subcomplex of D_{3,5} in which slot 5 may occur only in row i, for i=1,2,3. Every configuration belongs to some A_i. Every pairwise intersection, and the triple intersection, is the subcomplex D_{3,4} in which slot 5 is absent.

A_i strongly deformation retracts onto the subspace with q_i=e_5: interpolate q_i linearly to e_5 and keep the other rows fixed. The other rows have zero in slot 5 and disjoint supports from the old q_i, so every intermediate configuration remains valid. The retract is D_{2,4}.

The map (q_+,q_-)->q_+-q_- is a homeomorphism from D_{2,4} to the zero-sum l1 sphere

    {z in R^4 : sum_s z_s=0, ||z||_1=2}.

Its inverse takes the positive and negative parts. Radial normalization identifies this polyhedral sphere with S^2. Thus each A_i is simply connected, and all their intersections D_{3,4} are connected. Van Kampen applied successively to these finite subcomplexes proves D_{3,5} simply connected.

Now form the associated bundle P x_{S3} D_{3,5} over X. Extend a section over the cells of X: choose values over vertices, extend over edges using path connectedness, and over 2-cells using simple connectedness. There are no higher cells. This proves an equivariant map P->D_{3,5}, hence a five-state native stochastic realization. Combined with Section 3 and Section 1, the exact stochastic width is 5.

## 5. The centered plane bundle and normalized signed width

Let V=P x_{S3} {z in R^3:sum_i z_i=0}. The actual monodromy lies in C3, so V is oriented, and the generator acts by a plane rotation of angle plus or minus 2pi/3. Let b generate H^1(X;Z/3). The associated oriented plane is the underlying real bundle of the complex line with that root-of-unity holonomy. Its Euler class is

    e(V) = plus or minus beta(b) in H^2(X;Z),

where beta is the Bockstein for 0->Z --times3--> Z ->Z/3->0. This can also be read directly from cellular logarithms: lift the degree-1 mod-3 cocycle to integer value 1 on the 1-cell; its coboundary on the 2-cell is 3, so the integer Euler cocycle is 1. Cellular cochains give H^1(X;Z)=0 and H^2(X;Z)=Z/3, making beta an isomorphism. Thus e(V) is nonzero of order 3, and V is not trivial.

In contrast H^2(X;Z/2)=0 because the cellular differential is multiplication by 3, which is an isomorphism mod 2. The oriented rank-3 bundle V+epsilon has no obstruction to a frame on a 2-complex: its only obstruction lies in H^2(X;pi1(SO3))=H^2(X;Z/2)=0. Consequently V+epsilon is trivial. Thus V embeds in epsilon^3 but not in epsilon^2; its least trivial containing dimension g(V) is 3.

For completeness, normalized signed width is g(V)+1 for every compact persistent p-atom IID family, not just this example. Take the finite feature list of all words of lengths <=p-1, and let O be the p-by-M matrix of their atom evaluations. Polynomial interpolation gives rank O=p at every point. Put

    C_{uv}=f(uv)-f(u)f(v)=O^T (diag(w)-ww^T) O.

This is PSD of rank p-1, and its image bundle is isomorphic to V, by O^T on the standard zero-sum subspace. Given any normalized signed native competitor, define rows A_u=rho N_u-f(u)rho and columns B_v=N_v1. Then C=AB and A1=0. For z in im(C), z^T A=0 would imply z^T C=0; symmetry and positive definiteness on im(C) force z=0. Hence z->z^T A embeds V into 1_k^perp=epsilon^(k-1). This proves the lower bound against arbitrary signed native competitors, including nonminimal and unreachable ones.

Conversely, let j:V->1_k^perp be a bundle embedding and choose a continuous fiberwise left inverse j*. Split local component row vectors as z=(z1_p)pi_p+[z-(z1_p)pi_p], with pi_p uniform. Define the row-linear maps

    Q(z)=(z1_p)pi_k + j(z-(z1_p)pi_p),
    L(y)=(y1_k)pi_p + j*(y-(y1_k)pi_k).

They are equivariant, normalized, signed, and QL=I_p. The usual kernels L M_y Q and initial row wQ descend and realize the target. Thus normalized signed width is 4 in the Moore example.

## 6. Four strictly positive observable outputs suffice

Choose an isometric embedding j:V->epsilon^3, available from the triviality of V+epsilon. Let A:R^3->1_4^perp be a fixed linear isometry, c=(1,1,1,1)/4, and choose 0<delta<1/4. On the component-frame cover define

    v_i(p)=c + delta A j_x([p,e_i-(1,1,1)/3]).

The centered vector e_i-(1,1,1)/3 has norm sqrt(2/3)<1. Hence every coordinate of v_i is strictly positive and the coordinates sum to 1. The three vectors are distinct, their labels transform by the prescribed cover, and equal weights give a well-defined continuous observable law on X. The finite feature rank is 3; indeed these three points are already affinely independent because j is injective on the centered plane.

The full rank-3 response bundle is epsilon+V and is trivial. Therefore a varying-terminal real realization has width 3. One must not call the signed width 4 without retaining the fixed-terminal/normalized convention: this example makes that distinction essential.

## 7. Audit of an observable-only hypothesis

A continuous consistent exchangeable all-word law over a finite alphabet, with constant finite Hankel rank p, supplies the assumed p-atom mixture and cover without a hidden-model premise.

By de Finetti, at each x there is a unique probability measure mu_x on Delta(Y) with f_x(w)=integral m_w dmu_x. The Hankel matrix is the PSD Gram matrix of polynomial monomials. A p-point support gives rank p by polynomial interpolation. Conversely, if the support has at least r points, choose a linear functional separating r selected support points. The polynomials 1,t,...,t^(r-1) are independent in L2(mu): a polynomial which is zero mu-a.e. is zero on the support by continuity, hence has those r distinct roots. Thus the Hankel rank is at least r. Finite rank p is therefore equivalent to exactly p support points with positive weights.

Continuity of all word moments implies weak-* continuity of mu_x because polynomials are uniformly dense on the compact simplex. Around a basepoint, choose p disjoint small neighborhoods of its p atoms and nonnegative continuous test functions supported there with positive integrals. Nearby measures have an atom in each neighborhood. Since each nearby measure has exactly p atoms, there is exactly one in each and none elsewhere. Their positions and weights vary continuously, for example by taking normalized first moments against bump functions which equal 1 on smaller neighborhoods. This supplies local labelled atom charts and a principal frame cover. Compactness then supplies the positive minimum separation and weight used above.

The hypothesis must concern the complete exchangeable law, not an arbitrary finite table. Finite data alone do not certify exchangeability, extension to all horizons, or closure at the asserted rank.

## Sources checked

- Babson and Kozlov, Complexes of graph homomorphisms, Israel J. Math. 152 (2006), 285-312, Proposition 4.5: Hom(K_m,K_n) is a wedge of (n-m)-spheres. Section 2.3 also identifies Hom(K_{n-1},K_n) with the vacancy-swap Cayley graph. https://arxiv.org/html/math/0310056v4 ; source PDF https://arxiv.org/pdf/math/0310056 . The special simple-connectivity proof above is independent and fully explicit.
- Allen Hatcher, Vector Bundles and K-Theory, version 2.2, printed page 75 (PDF page 78): the framing obstruction on a 2-complex is Euler class for oriented rank 2 and w2 for oriented rank >=3, and is complete on the 2-skeleton. Proposition 3.10 gives complex-line classification by c1; Proposition 3.13 relates Euler and Chern classes. https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf .
- The supplied Double_Cover_Realization.tex, buffered decoder repair theorem, supplies the explicit equivariant decoder construction needed for the stochastic upper bound. No arbitrary-native higher-rank result is attributed to that existing theorem.
