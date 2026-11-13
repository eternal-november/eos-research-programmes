# Independent proof: arbitrary native HMM to a disjoint-support cover certificate

## Scope
Let X be compact Hausdorff (the application is a finite 2-complex). Over X, let C be a p-sheet component cover whose fibres are distinct probability vectors v_i(x) on a fixed finite alphabet Y. Let w_i(x)>0 be continuous component weights summing to one, transported together with the components. The observable law is exactly the held IID mixture p_x(u)=sum_i w_i product_{symbols a in u}v_i(a). No stationary initialization of a competing HMM is assumed. A competitor has fixed k labels, continuous probability row rho and nonnegative outcome matrices N_y, with sum_y N_y row stochastic.

Claim: a continuous k-state competitor exists iff the component frame bundle admits an equivariant map to D_{p,k}, the space of p probability rows on k labels with pairwise disjoint supports. Equivalently it admits a continuous split stochastic pair Q,L with QL=I_p. The proof below extracts a split pair from arbitrary HMMs without identifying recurrent classes or assuming component-preserving state maps.

## Uniform continuous classifier
The minimum pairwise component separation delta in sup norm is positive by compactness. Put m=|Y| and choose a continuous bump phi with phi(t)=1 for t<=delta/8 and phi(t)=0 for t>=delta/4, with values in [0,1]. For a length-n word u let f(u) be its empirical frequency vector and define, in any local ordering,

c_i(x,u)=phi(||f(u)-v_i(x)||_infty)+(1-sum_j phi(||f(u)-v_j(x)||_infty))/p.

At most one bump is nonzero. Therefore these c_i form a continuous equivariant probability vector. If f(u) is within delta/8 of v_i then c_i=1. Let A_li=E_{v_l^{tensor n}} c_i. Hoeffding and a union bound give A_ii>=1-eta and A_li<=eta for l!=i, uniformly in x, whenever 2m exp(-2n(delta/8)^2)<=eta. Rows of A sum to one. Let w_min>0 be the minimum component weight.

## Two-block extraction
For the competitor define

R_i = rho sum_{|u|=n} c_i(x,u) N_u,
a_i=R_i 1,
Q_i=R_i/a_i,
L_{j,i}=sum_{|z|=n}c_i(x,z)(N_z 1)_j.

All terms are continuous in local component coordinates and equivariant under relabelling. Q and L are row stochastic. Moreover a_i=sum_l w_l A_li>=w_min(1-eta)>0; zero initial coordinates cause no problem.

The hidden Markov factorization and conditional independence of the held-mixture past and future give

(QL)_{i,h}=[sum_l w_l A_li A_lh]/a_i.

Thus

1-(QL)_{i,i}=[sum_l w_l A_li(1-A_li)]/a_i <= eta/[w_min(1-eta)].

Taking eta<=w_min/8 gives a bound <1/4. In particular every diagonal entry of QL exceeds b=3/4. This calculation uses only length-n and length-2n probabilities, though the target model class itself is an all-word promise.

## Exact split repair
Choose a=2/3 and b=3/4. Let s(t)=0 for t<=a, s(t)=(t-a)/(b-a) for a<t<b, and s(t)=1 for t>=b. For a decoder row l in Delta^{p-1}, set

r(l)=(1-sum_i s(l_i))l+sum_i s(l_i)e_i.

Because a>1/2, at most one s(l_i) is positive. Hence r is a continuous permutation-equivariant map of the simplex to itself and r(l)=e_i whenever l_i>=b.

Define

Q'_{i,j}=Q_{i,j}(L_{j,i}-b)_+ / sum_h Q_{i,h}(L_{h,i}-b)_+,
L'_j=r(L_j).

Every denominator is positive because (QL)_{i,i}>b. If Q'_{i,j}>0 then L'_j=e_i. Consequently Q'L'=I_p exactly. This proves arbitrary-HMM necessity, including transient states, inactive labels, and changes of recurrent structure.

## Sufficiency from D without a decoder selection assumption
Given a continuous equivariant disjoint-support Q in D_{p,k}, choose 0<theta<1/k and set

Q'_{i,j}=(Q_{i,j}-theta)_+ / sum_h(Q_{i,h}-theta)_+.

Each denominator is positive since a row maximum is at least 1/k. Let f(t)=min(t/theta,1), pi=(1/p,...,1/p), and define

L_j=sum_i f(Q_{i,j}) e_i + [1-sum_i f(Q_{i,j})]pi.

At most one Q_{i,j} is nonzero, so L_j is stochastic. If Q'_{i,j}>0 then L_j=e_i. Thus Q'L=I_p. The formula is continuous and equivariant even where slots become vacant. It need not lift the original Q exactly; truncation is the essential repair.

For a split pair, put M_y=diag(v_1(y),...,v_p(y)), N_y=L M_y Q', and rho=w Q'. These descend to globally labelled k-state kernels. Their sum LQ' is stochastic. Telescoping Q'L=I gives rho N_u 1=sum_i w_i product v_i, for every word. An ordinary transition-then-emission HMM is also available with T=LQ' and E=LV.

## Moore-space cross-check
For p=3,k=4, D_{3,4} is a graph. It has 24 labelled vertices and 36 labelled edges. The free S3 quotient has four vertices indexed by the vacant native slot and one edge for each pair of vacancies: it is K4. A C3 quotient has 8 vertices and 12 edges and is also a graph. The nontrivial three-sheet cover of X=M(Z/3,1) cannot be pulled back from a graph, since any homomorphism Z/3 into a free group is trivial. Therefore four labels are impossible by the arbitrary-HMM necessity just proved.

For p=3,k=5, D_{3,5} is simply connected by the established wedge-of-(k-p)-spheres theorem of Abrams-Gay-Hower. Equivariant cellular extension over the free 2-dimensional C3-cover gives a map to D_{3,5}. The explicit truncation/decoder formula above produces a five-label native model. Thus the stochastic width is exactly five, conditional only on supplying an observable three-component family representing that cover.

## Constructing positive emissions and signed comparison
The centered plane E of the C3 permutation representation has Euler class generating H^2(M(Z/3,1);Z)=Z/3. Thus E is nontrivial. Its oriented rank-three stabilization R+E is trivial: H^2(X;Z/2)=0 and oriented rank-three bundles over a 2-complex are classified by w2. Embed E in the trivial R^3 identified with the zero-sum subspace of R^4. The three canonical centered vertices e_i-(1/3)1 of the permutation bundle, sent through this embedding and scaled sufficiently small, give three strictly positive affinely independent emissions near the uniform vector in Delta^3. Uniform weights yield the required observable family. Pointwise minimum is three by Hankel rank. Fixed-normalization signed width is four: width three would trivialize E, and the embedding E->R^3 supplies four normalized signed coordinates. Unconstrained real width is three because R+E is trivial.

The last bundle facts should receive a dedicated topology review and source attribution; the arbitrary-HMM bridge and decoder formulas above are independent of them.

## Sources and limits
- Abrams, Gay, Hower, Discretized configurations and partial partitions, https://arxiv.org/abs/1009.2935. Its configuration spaces are established prior art.
- Hazewinkel and Perdon, On the theory of families of linear systems, https://ir.cwi.nl/pub/10111/10111D.pdf. Parameterized state bundles are established prior art.
- Existing Monodromy_Realization.tex records the Heller/Anderson/Vidyasagar/Monras-Winter positive-realization controls. This note is an independent mathematical derivation, not a novelty audit.

## Independent review of observable_exchangeable_width.tex (2026-11-03 23:49 UTC)
Reviewed the full draft at observable_research/observable_exchangeable_width.tex. No blocker found in: de Finetti reconstruction and constant-rank support cover; intrinsic positive cone; uniform classifier epsilon_n=2d exp(-n delta^2/32); n>=ceil(32 delta^{-2}log(16d/w_*)); diagonal near-split bound 6/7; exact-split denominator 3/28; D-to-split denominator 1/2; total variation obstruction w_*/64; normalized signed lower bound using invertible classifier matrix; normalized signed upper construction.

Important HMM convention correction: T diag(E_:y)=L D_y Q exactly for T=LQ,E=LV. The reverse product diag(E_:y)T generally differs on vacant mixed-decoder rows. Nonetheless it gives the same observable law with rho=wQ, since Q diag(E_:y)T=D_y Q. Thus both ordinary state-emitting timing conventions admit same-width realizations, but matrix equality must not be confused with equality of the observable law. This was sent directly to the author and parent.
