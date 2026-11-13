# Discovering a dynamic product atlas from noisy local observations

## Status and purpose

This is a research manuscript reviewed independently by AI on 28 October 2026; no Lean or external human verification is claimed. It gives a population construction and a finite-data stability statement under explicit margins. The statistical statement below includes explicit local error transfer and a finite-sample wrapper with a rigorously finite calibration-conditioning constant. That constant is defined through a fixed-dimensional compact inverse problem rather than a supplied numerical formula; no production implementation or practical sample bound is claimed. It does not claim that the algebraic identification lemmas are new. The main construction does not begin with a supplied correspondence between observation ports and component states. Observation patches may contain several components, their latent alphabets are unknown, and a component may occur in only one patch. In particular, singleton-exposing overlap covers are not required.

The key step is temporal. After identifying a finite hidden patch alphabet from three noisy views, the construction identifies its product coordinates from families of conditional next-state distributions. A static overlap such as patches {a,b} and {b,c} exposes b but leaves arbitrary b-dependent relabelings of a and c. Temporal product constraints can rule out these relabelings. The inferred coordinates are local stochastic mechanisms, not necessarily dynamically independent processes: their transition kernels can depend nonlinearly on other mechanisms and on delayed states.

## 1. Declared model universe and observation access

There are unknown nontrivial finite alphabets X_a, a in an unknown finite index set A. Write r_a=|X_a|>=2. The hidden process has maximum lag L and transition law

  P(X(t+1)=x' | X(<=t)) = product_a K_a(x'_a | x_{Pa_a}),

where Pa_a is an unknown set of at most d pairs (b,ell), ell in {0,...,L-1}. The entry x_(b,ell) means X_b(t-ell). Every entry of every K_a is at least kappa>0. Thus the next-coordinate innovations are conditionally independent, but arbitrary nonlinear, cyclic, delayed interactions are allowed. An unobserved shared influence is permitted as another coordinate; correlated fresh innovations not represented in this way are outside this universe.

The process is stationary. Its lag-state chain has a unique full-support stationary distribution: over L steps every target lag history has positive probability, so the L-step transition matrix is strictly positive. No uniform-in-size mixing rate follows from this fact alone.

The observation protocol supplies m named patches, not their component ownership. Patch p has an unknown subset S_p of A, with at most w atoms, and hidden patch state Q_p=product_(a in S_p) X_a. Every atom occurs in at least one patch. Constant latent patches (R_p=1) may be discarded after calibration, or represented by the empty Cartesian profile; they carry no nontrivial component. For the remaining patches write R_p=|Q_p|<=R, where R is a declared bound. The map from the hidden tuple to the learner's recovered patch labels is unknown. There is no assumed separating/intersection structure on {S_p}; private factors and nested incidence patterns are allowed.

At each observed tick, patch p can be read through three categorical sensor views. Conditional on the whole hidden trajectory, all sensor draws are independent across patches, views and time. Their conditional distributions depend only on Q_p(t). The three unknown emission matrices E_p^j have stochastic columns and full column rank R_p. Strictly positive emissions are allowed and desirable: an individual readout then never reveals the hidden state. Full column rank is statistical invertibility, not instantaneous decoding; arbitrary rank-deficient sensing is not covered.

Population access means exact laws of bounded collections of simultaneous or temporally aligned sensor readings. Finite-data access means independent stationary windows for each requested mask, or an independently justified concentration/mixing guarantee for the recorded trajectory. One must not combine separately sampled patch records as if they were joint observations. Required masks involve a bounded number of patches and at most L+1 ticks. No reset exposes membership or hidden state.

The identified target is the finest factorization justified by conditional transition rows, not an arbitrary original grouping of coordinates. Merging several elementary mechanisms remains valid, and a nominal six-state module that itself factorizes as two-by-three is not intrinsically one atom. Regional grouping choices remain a separate discovery question.

The input includes bounds R,w,d,L and quantitative margins where a statistical guarantee is wanted. It does not include A, S_p, r_a, the emission matrices, parent sets, local kernels, component regions, or boundary-state alphabets.

## 2. Local sensor calibration and latent patch laws

Let a patch's three-view law be

  T(y1,y2,y3)=sum_q pi(q) E1(y1,q) E2(y2,q) E3(y3,q).

Since pi(q)>0 and E1,E2 have full column rank, rank(T12)=R_p, so the unknown patch alphabet size is identified. Choose orthonormal column/row bases U,V for T12, making U^T T12 V invertible. For a vector z over the third sensor alphabet, form the contracted matrix T_z. Then

  (U^T T_z V)(U^T T12 V)^(-1)
   = (U^T E1) diag(E3^T z) (U^T E1)^(-1).

The columns of E3 are distinct. Some z therefore gives pairwise distinct eigenvalues. There is a bounded deterministic search: if the third sensor has s symbols, take z(t)=(1,t,...,t^(s-1)) for integer t from 0 through binom(R_p,2)(s-1). Every pairwise column difference gives a nonzero polynomial of degree at most s-1, so at most binom(R_p,2)(s-1) choices are bad. At least one contraction has simple spectrum. Singleton latent patches need no such search. Eigenvectors recover E1 up to permutation and scaling. Multiplication by U and normalization of each column to sum one resolves scaling. If L1 is a left inverse of E1, then

  pi=L1 T1,
  E2^T=diag(pi)^(-1) L1 T12,
  E3^T=diag(pi)^(-1) L1 T13.

Thus all three emissions and pi are recovered up to one patch-state permutation. This is the standard finite three-view mixture mechanism, used here as a lemma.

For any bounded tuple of patch-time variables, its observed law in view1 is obtained by applying the tensor product of their emission matrices to its latent law. Apply the corresponding tensor product of left inverses to recover that latent joint law. This remains valid for overlapping patches; their latent states need not be independent. The independent sensor draws, not independent hidden patches, justify the tensor product channel.

Every consistent cylinder fixing k hidden coordinate-time values has probability at least kappa^k. To see this, order the prescribed times, condition on the entire preceding history, and use conditional independence of simultaneous updates and the lower bound kappa, then integrate unprescribed coordinates. Consequently all nonzero probabilities of bounded latent patch contexts have a size-independent lower bound depending only on w,d,L,kappa. Duplicate/overlapping patch assignments can instead be inconsistent and have probability zero.

## 3. Discover sufficient temporal contexts before discovering coordinates

Let D=wd. A context B consists of at most D patch-lag pairs (p,ell), ell in {0,...,L-1}. For each target patch p, acquire the law of Q_p(t+1) jointly with the old context Q_B(t). Compute H(Q_p(t+1)|Q_B(t)) for every such B, and choose a minimizer B_p.

There exists a context B0 of size at most D containing every true parent coordinate of every atom in S_p: choose one covering patch for each parent-coordinate/lag pair. Therefore

  min_(|B|<=D) H(Q_p(t+1)|Q_B(t))
   = H(Q_p(t+1)|X(t),...,X(t-L+1)).

For any minimizing B_p, equality in conditional entropy implies

  P(Q_p(t+1)|Q_Bp(t))
   = P(Q_p(t+1)|X(t),...,X(t-L+1))

almost surely, and hence on every consistent finite history by full support. In particular each recovered conditional row is the true product of the atom update distributions inside the patch. This argument does not supply component ownership to the search. It also does not require minimizing contexts to be unique: two contexts may carry the same necessary information.

The number of acquisitions is O(m (mL)^D), and each latent table has at most R^(D+1) entries before accounting for overlaps. This is a local-in-system-size construction when R,w,d,L and sensor alphabet bounds are fixed. The exponent D is substantial, and is not presented as a practical algorithm for unbounded width.

## 4. Recover unknown product coordinates from the conditional row family

For a finite set Q and positive conditional rows p_c in the simplex on Q, define

  W = span_R( 1, log p_c : c ranges over positive-probability contexts ).

For a Cartesian labeling g:Q -> product_(j=1)^k Z_j, |Z_j|>=2, define

  V_g = { f:Q->R : f(q)=sum_j f_j(g_j(q)) }.

It contains constants and has dimension 1+sum_j(|Z_j|-1). A row p_c factors as a product over these coordinates if and only if log p_c belongs to V_g. The forward implication is immediate. Conversely exponentiation gives a product of positive factors, and normalization divides each factor by its own sum because the grid is a genuine Cartesian product.

**Dynamic richness assumption.** For each patch, the span W_p of its true conditional next-state rows equals the additive space V_true of its true atom coordinates. This is a testable rank/separation promise after a candidate grid is proposed. It expresses sufficiently diverse local mechanism responses; it is stronger than mere positivity. It need not require independent processes or linear dynamics.

Enumerate the finitely many ordered alphabet profiles with product R_p and the Cartesian bijections of Q_p into each profile. Retain those for which W_p is contained in V_g. Choose those with minimum dim(V_g). Under dynamic richness the minimum equals dim(W_p), and all minimizers have V_g=W_p.

**Grid rigidity lemma.** If two Cartesian labelings of the same finite set have the same additive function space, they differ only by permutations of coordinate factors and separate bijections of factor alphabets.

Proof. Map each q into the dual of the additive function space by evaluation, with the constant coordinate removed. Under either Cartesian labeling, the convex hull of these evaluation vectors is affinely a product of simplices. Its one-dimensional faces connect exactly pairs of vertices differing in one factor. This graph is therefore a Cartesian product of complete graphs. Its factor directions can be recovered intrinsically: put two edges in the same class if they lie in one triangle or are opposite edges of an induced four-cycle, and take transitive closure. In a product of complete graphs these relations never mix directions; triangles connect all edges of a factor fiber when its alphabet has at least three elements, and squares transport the direction between fibers. For a binary factor the fiber is a single edge and squares still transport it. Thus the edge classes are precisely the factor directions. Removing one direction's edges gives components indexed by that coordinate's values. Both labelings recover exactly these same quotients, up to permutation and alphabet bijection. QED.

This identifies unknown patch factor count, cardinalities and state-coordinate maps. These are maps on the inferred latent patch alphabet, not functions of one noisy sensor reading. No real-time decoding, filtering, controller observation access, or physically available boundary state follows from this calibration theorem alone. Neither patch intersections nor the sensor protocol have to expose an individual component. A private coordinate can be identified by its temporal product structure.

The lemma is a finite product-rigidity result, not a novelty claim; tensor-preserver and Cartesian-product graph results are relevant precedents. Exhaustive local Cartesian enumeration costs a function of R, not a function exponential in the number of global atoms.

### Why rich rows exist in nonlinear interacting growing families

Start with atom kernels whose output log odds vary with their own previous state through r_a-1 linearly independent functions. Across a patch, varying the old coordinate tuple independently gives full additive log-row span. Add sufficiently small strictly positive nonlinear dependence on neighboring coordinates or delayed neighbors. Full row rank is an open condition, so it persists while each added interaction is genuinely nonzero and the kernels remain positive. This provides growing coupled families satisfying the condition; it is not a proof that every nonlinear sparse process satisfies it.

### A weaker generic product-separation alternative

The full log-span assumption is a convenient sufficient condition, not necessary. The companion Product_Factor_Rigidity.md proves: a bijection between finite Cartesian sets preserves every positive product distribution exactly when it merges disjoint groups of input factors and relabels each merged group. Therefore every candidate Cartesian recoding that is not a true coarsening violates a coordinate-versus-rest rank-one minor on some positive product row. Since there are only finitely many bounded patch recodings, one generic positive product row excludes all noncoarsenings.

The preferred weaker hypothesis is that the observed sufficient conditional row family separates every noncoarsening recoding: each such recoding has at least one nonzero rank-one minor in some row. Accept all local grids whose rows factor, then choose the finest, equivalently the smallest additive dimension among these coarsenings. The true elementary grid is the unique finest one up to factor permutation and independent alphabet relabeling. Multiple rows can jointly provide separation even if none does alone. This condition has a quantitative version using the minimum over bad recodings of their maximum absolute tested minor.

This genericity can be established within the declared unrestricted sparse-kernel parameter family, rather than only in an unrelated family of distributions. Fix one full old history, for example one chosen symbol at every coordinate and lag. For each atom, the output probability row at its associated local parent configuration can be varied freely in the positive simplex, independently of the other atom tables. Thus the product probabilities of every target patch at this history range over the full product-simplex family. A bad recoding's nonzero minor polynomial is therefore not identically zero in the actual kernel parameters. The union of the bad loci over finitely many patches and recodings is proper and measure zero. Essential nonlinear dependencies can simultaneously be imposed by avoiding their own proper equality loci. Parameter-sharing constraints may destroy this freedom and must be checked separately. Quantitative distance from the bad loci is still needed for finite-data recovery.

This argument does not canonize an arbitrarily declared input factorization: the assumption excludes further splits not supported as elementary factors by the mechanism family. Without it the accepted factorization family, not the author's chosen grouping, is the object to retain.

### Degenerate cases

Without richness, retain all Cartesian labelings satisfying W_p subset V_g rather than declare a unique finest physical ontology. A private-coordinate relabeling dependent on an overlap coordinate can preserve some special row families. Local accepted grids still require cross-patch alignment and joint dynamic checks; independent acceptance is not a global realization theorem. The generic theorem does not claim to classify every such degenerate global family. Coarser groupings remain admissible even in the rich case; the theorem identifies elementary innovation coordinates, after which useful interacting regions and interfaces must still be discovered.

## 5. Align dynamically discovered factors between patches

For each pair of discovered patch factors, recover their same-time joint law using the calibrated patch sensors and the learned quotient maps. Two appearances of the same hidden atom are related by a deterministic bijection. Two different atoms have full Cartesian support, by positivity of the hidden process. Therefore equality up to a bijection is recognized exactly by the support graph being a perfect matching rather than a full rectangle.

Merge factor appearances linked by such bijections, propagating their alphabet relabelings. All cycle composites are the identity in the promised model. A nonidentity composite is a certificate that the proposed atlas does not identify one consistent shared variable. Private factors form singleton classes. No two different factors of one patch may be merged. The product of the learned factor maps on each patch must be bijective; this is directly checked.

The result is the global unknown atom index set A, its alphabets and patch incidence, up to global coordinate permutation and within-coordinate relabeling. This is an atlas of local coordinates, not an enumeration of the global product alphabet.

## 6. Discover local nonlinear delayed mechanisms

Now use any containing patch as a readout for each learned atom. For target atom a, consider every set S of at most d atom-lag variables. Recover the conditional entropy H(X_a(t+1)|X_S(t)). Its minimum equals the conditional entropy given the full lag state, since the true parent set is among the candidates.

Choose an entropy minimizer of smallest cardinality. It is the unique essential parent set: if another sufficient set omits an essential variable, full support allows two histories agreeing on that set but having different target update distributions, contradicting sufficiency. Remove inessential arguments from the original Pa_a when defining this target. The conditional probability table gives K_a. This argument learns both delay and parent ownership within the declared lag bound.

The total acquisition count is O(|A| (|A|L)^d), using at most d+1 containing patches per table. Unknown observation-patch topology and private coordinates do not change this bound. The resulting independent-coordinate update kernels specify a positive global process compactly. Conditional innovation independence is a model-class promise, not something certified against arbitrary outside processes by these low-order tables.

## 7. Discover recursive boundary states on bounded regions

Let S be any candidate region of at most b learned atoms. Its internal physical state Z_S is its L-tick history register, with at most R^(bL) values. Let u collect the admitted values of external parent-lag variables needed to update S. The learned kernels define a controlled transition T_S(z'|z,u): sample the fresh states using the product atom kernels and shift the old registers. These history transitions have structural zeros from shifting even though the fresh kernels are positive.

Define the outgoing response signature h_S(z) by the list of all receiver-kernel rows outside S that depend on S, evaluated at every admissible assignment of their other arguments. Two internal states have the same h_S precisely when substituting one for the other preserves all those immediate outside update distributions.

A deterministic autonomous interface is a surjective map q:Z_S->B such that h_S factors through q and, for every admitted input u and every block B0 of q,

  sum_(z' in B0) T_S(z'|z,u)

is constant on each fiber of q. This is controlled strong lumpability plus outgoing-response sufficiency. It permits a recursive boundary process driven by incoming interface values. It is stronger than merely having equal current outgoing responses.

Start from the partition induced by h_S. Repeatedly split a block whenever two of its states have different transition probabilities to a current block under some admitted input u. The finite refinement stabilizes in at most |Z_S|-1 strict splitting rounds. The terminal partition is the coarsest controlled strongly lumpable partition refining h_S. Proof: any admissible q must refine the initial partition, and an induction shows it must refine every split, since sums to unions of its blocks are constant. The fixed point itself satisfies the defining conditions.

Thus its number of blocks is an exact lower bound, attained by the construction, for deterministic autonomous state-summary interfaces under this input/output contract. It is not a lower bound for all stochastic encodings, all protocols, or physical storage newly added to the source. The source already stores Z_S; shared registers must be counted once. Changing the permitted input observations or communication timing can change the answer.

All regions |S|<=b can be searched without enumerating the full global state space. The candidate region count is O(|A|^b). The local state-space refinement cost depends on b,L,d and alphabet bounds; constructing each outgoing signature additionally scans its outside receivers and their local argument assignments. With unbounded outdegree this costs a further polynomial factor in |A|, not a constant depending only on the local bounds. A resource budget can filter the resulting decompositions; no single region or partition is forced when several are valid.

## 8. Coupled realization and crossings

A summary update is coupled to its source transition by setting B'=q(Z'_S) on the very same next-state draw. Independently sampling a quotient transition with the correct marginal can destroy source-summary correlation. Therefore every witness retains old/new source states, the sampled atom transitions once, and summary aliases.

For two overlapping region summaries q_S and q_T, separate lumpability does not suffice for an autonomous joint summary. The joint pushforward distribution of (q_S(Z'_S),q_T(Z'_T)) must be constant on the fibers of the retained joint state and admitted boundary inputs. This is a finite test on the bounded union of the regions and their parents. If it holds, its common pushforward kernel is the unique joint transition compatible with every representative. If it fails, two representatives with identical retained summaries and different joint next-summary laws witness the obstruction. Further partition refinement can construct the coarsest required union summary, subject to the chosen boundary contract.

Complete atom-record regroupings always have a common coupled realization within the promised model. Budget-limited summary-only realizations may fail. These are different claims. The companion gluing note supplies the detailed criterion and examples.

## 9. Finite data and what is actually certified

For fixed local bounds, the construction involves polynomially many bounded-dimensional observed probability tables. A quantitative theorem assumes: lower nonzero singular values for sensor calibration; an eigenvalue gap for the chosen three-view contraction (or a robust tensor decomposition condition); lower probabilities for consistent local contexts; a positive conditional-entropy gap separating sufficient from insufficient bounded contexts; a log-row rank gap and a positive separation from competing local Cartesian grids of dimension no larger than the true additive dimension; and positive gaps for essential parent and boundary-partition distinctions.

Uniform estimates of all requested observed tables, including those used for model selection, then imply correct discrete structure with high probability and controlled errors in emissions and local kernels by finite-dimensional perturbation bounds. Independent stationary windows give standard finite-alphabet concentration and a logarithmic union bound over the polynomially many requests. Data reuse is legitimate only with uniform concentration, or with a separate validation split. A single trajectory needs its own dependence analysis; positivity alone is insufficient for a polynomial mixing claim.

Exact zeros, equality of transition rows and minimal cardinalities are unstable without separation. When margins are unavailable, retain a confidence family of local tables and compatible grids rather than assert a unique exact architecture. Producing a complete efficient global representation of this ambiguous family is a separate obligation, not supplied automatically by the rich-case theorem.

### Uniform sensor-calibration stability on a fixed conditioning class

Fix latent rank r, sensor alphabet sizes at most s, a mixture-weight floor pi0>0, and a sensor singular-value floor sigma>0. Let C be the compact parameter class of stochastic sensor matrices with smallest singular value at least sigma and mixture weights at least pi0. Strictly positive sensor entries can additionally be imposed through a fixed positive floor, but nonnegative entries suffice for this argument. The forward map Phi:C->probability tensors is polynomial and injective up to simultaneous latent-label permutation.

Its inverse is locally analytic modulo labels. A direct chart construction avoids arbitrary singular-vector bases: choose an invertible r-by-r minor M=T12[I,J]. Then T_z[I,J] M^(-1) is similar to diag(E3^T z) by E1[I,:]. Choose one of the finite moment-curve contractions with distinct eigenvalues. Spectral projectors, the extension T12[:,J]M^(-1), and column normalization reconstruct E1 analytically in a neighborhood where the chosen minor, eigenvalue gaps and normalization denominators remain nonzero. The other parameters follow by the left-inverse formulas. When selecting a projector column, choose one that is nonzero; finitely many columns suffice. Rank-one latent patches are recovered directly by marginals.

These local inverse neighborhoods cover Phi(C), a compact set. A finite subcover with smaller neighborhoods bounds all inverse derivatives. Nearby tensors therefore obey one common Lipschitz bound; pairs farther apart obey a bound from the compact parameter diameter divided by a positive neighborhood radius. Consequently there is a finite constant C_cal(r,s,pi0,sigma) such that, for any theta,theta' in C,

  min_labelpermutation ||theta-theta'||_1
    <= C_cal ||Phi(theta)-Phi(theta')||_1.

The metric on parameters is the sum of entrywise one-norms of the weight vector and the three emission matrices. This establishes finiteness, not a numerically sharp expression for C_cal. The finite chart/minor choices and the compact class are part of its definition; no constant depends on the total number of patches.

Given an empirical tensor within delta in one-norm of its true value, choose a minimum-distance fit in C. A minimizer exists by compactness. Its forward error against the true tensor is at most 2delta, hence its parameter error after relabeling is at most 2 C_cal delta. A fit within optimization tolerance delta adds a further delta to this factor; for definiteness the statements here use an exact minimizer or adjust the factor accordingly. This is a fixed-dimensional polynomial optimization problem, not an assumption that raw spectral estimates are valid probabilities.

The unknown rank is first selected from T12. Its nonzero singular values are at least pi0 sigma^2. If delta<pi0 sigma^2/2, thresholding at pi0 sigma^2/2 separates them from noise singular values (strict inequalities can be used at the threshold). The calibrated class for the selected rank contains the truth.

For final calibrated matrices in C, choose Moore-Penrose left inverses. Their induced one-norms are at most B=sqrt(R)/sigma. If emission-matrix entrywise one-norm error is e_E, the inverse difference is at most

  sqrt(R) (sigma^(-2)+2R sigma^(-4)) e_E

in induced one-norm. Indeed expand (E^T E)^(-1)E^T, use the inverse-Gram identity, ||E||_2<=sqrt(R), and convert operator two-norm to column one-norm. Thus one may take

  eta = 2 sqrt(R) (sigma^(-2)+2R sigma^(-4)) C_cal delta.

This supplies the calibration premise in the transfer bounds below. It is conservative and uses a valid fitted calibration, not unnormalized eigendata.

### Explicit local error transfer once sensors are calibrated

Use the induced vector one-norm. Suppose every true sensor left inverse has norm at most B>=1, each estimated inverse differs by at most eta, and each requested observed k-way probability table has one-norm error at most delta. Deconvolving with the estimated tensor-product inverse gives latent one-norm error at most

  zeta0=(B+eta)^k delta + k eta (B+eta)^(k-1).

The first term propagates the observed-table error. The second is a telescoping tensor-product difference applied to a probability vector. Projecting to the probability simplex in one-norm raises the bound to at most zeta=2 zeta0, since the true law is feasible. Here k is bounded by D+1 (or the other fixed mask sizes), never by the total number of atoms.

For a consistent context of probability at least s, if zeta<s/2, the reconstructed conditional row has one-norm error at most 4 zeta/s. A rank-one minor therefore has error at most 16 zeta/s. If the product-separation gap is Delta, threshold separation is possible when 32 zeta/s<Delta.

For entropy selection, define F_M(t)=t log(M-1)+h2(t) for M>=2 on its usual small-error range, and F_1(t)=0 for a singleton alphabet. A joint/context table of alphabet sizes at most M_joint and M_context and one-norm error zeta changes conditional entropy by at most F_Mjoint(zeta/2)+F_Mcontext(zeta/2). An insufficient-context entropy gap greater than twice this bound guarantees that an empirical entropy minimizer is genuinely sufficient; this is enough for the patch-context step, which does not require a smallest context. Minimal-parent selection needs an additional tolerance rule: let E be the uniform entropy error, retain all candidates within tau of the empirical minimum with 2E<=tau<Delta-2E, and then choose the smallest cardinality. This requires Delta>4E, includes every truly sufficient candidate, excludes every insufficient one, and recovers the essential parent set. Choosing the smallest among exact empirical minimizers alone is unsound because sampling fluctuations can prefer a superfluous superset. Support identification requires entrywise error smaller than half the nonzero support margin.

Empirical inversion need not produce probabilities. The simplex projection above is therefore part of the procedure, not optional. After coordinate/parent selection, project each estimated local kernel row onto the stochastic simplex with entries at least kappa/2 (assuming the declared kappa is known). The true row is feasible, so nearest one-norm projection increases its one-norm error by at most a factor two. Thus e=8 zeta/s is a valid conservative bound for final local-kernel row error when the preprojection conditional bound is 4 zeta/s. Calibrated sensor columns must likewise be stochastic; the inverse-error premise applies to inverses built from the final valid sensor estimates, not to arbitrary unnormalized eigenvectors.

For a region containing b atoms, the induced fresh-state product transition has row total-variation error at most b e/2, and its deterministic history shift does not increase the error. Consequently a sum of transition probabilities to any fixed partition block has error at most b e/2; comparing two old states has error at most b e. If every nonzero block-sum difference relevant to partition refinement is at least Delta_B and 2 b e<Delta_B, a threshold between b e and Delta_B-b e recovers the exact splitting decisions. The initial outgoing-signature comparison has pairwise entry error at most 2e; an initial-signature gap exceeding 4e suffices. One can state Delta_B uniformly over the finitely many partitions of the bounded source-history set, or only over the exact refinement stages. The same bound with the size of a bounded union replaces b in crossing-summary tests. No uniform such gap follows from positivity alone.

Under correct atom identification and a common initial lag-history law, local-kernel row error e implies H-step whole-process total variation at most min(1,H |A| e/2), by conditional product coupling and a union bound across time. An initial-law error epsilon0 is added. Observing through a common sensor channel cannot enlarge the distance; estimated sensor channels require their own additional coupling term. The theorem does not identify or cheaply sample the stationary initial law by this argument. The gluing note gives one optional Dobrushin condition and charged burn-in construction.

For raw empirical observed tables with J outcomes, N independent windows and failure allowance alpha, coordinate Hoeffding plus a union bound gives one-norm error at most J sqrt(log(2J/alpha)/(2N)). A further union bound covers all polynomially many requested tables. Calibration must also use independent or uniformly controlled three-view records. The compact-class bound above supplies eta as a function of their raw-table error. The result is a finite-sample theorem with a defined conditioning constant, not a numerically evaluated sample budget.

### High-probability sampling wrapper

Let Q be the number of raw probability tables requested, including calibration, sufficient-context search, pair alignment and parent search. For fixed local width and alphabet bounds, Q is polynomial in the number of patches. Let J be the largest raw table alphabet size. Choose delta_star>0 small enough that the rank threshold, support margin, context/parent entropy tolerances, product-minor gap and any requested interface-partition gap inequalities above all hold after substituting eta=2 sqrt(R)(sigma^(-2)+2R sigma^(-4)) C_cal delta_star and the resulting zeta. Such a positive delta_star exists when the stated gaps are positive. All table sizes, conditioning constants and relevant local dimensions are fixed in this choice.

With N independent stationary windows per requested table, it suffices to take

  N >= J^2 log(2 J Q / alpha) / (2 delta_star^2)

to make every raw table's one-norm error at most delta_star with probability at least 1-alpha, by the coordinate Hoeffding bound and a union bound. On this event the fitted calibration, finest separated product atlas, support alignments, essential parent sets and gap-separated deterministic boundary partitions are recovered up to labels, and the displayed probability-error bounds hold. Parent selection uses the near-minimum tolerance rule, not exact empirical ties. These are uniform events over all bounded raw masks used by the adaptive construction; one can acquire them before model selection, or use fresh validation data.

Thus the sample count and local computational work are polynomial in system size at fixed widths and fixed quantitative conditioning/separation bounds. They can be prohibitive in those bounds. Compact minimum-distance calibration is a mathematical estimator, not an implemented scalable routine. A numerical precision model and optimizer tolerance must be charged in an implementation; the theorem is not a bit-complexity claim for exact real arithmetic. No such finite-sample guarantee is uniform near nonidentifiability, rank loss or vanishing excitation.

The checker is conditional on the declared model universe. It does not certify that an arbitrary real environment has independent hidden innovations, finite lag, full-rank repeated sensors, or no additional hidden hazard. Nor does the theorem identify causal effects of unrecorded or confounded interventions from passive observations.

## 10. An unresolved-atlas theorem without generic coordinate identification

The generic theorem is not the only output. Sections2–3 identify the patch alphabets and sufficient patch transition rows without any product-separation assumption. Enumerate all bounded Cartesian charts of each patch whose full conditional next-patch rows factor. Retain all charts with coherent factor identifications across patches reproducing every pair support, including identity around cycles. The companion gluing/Positive_Atlas_Gluing.md proves that these local tests are globally sufficient within the declared universe.

The key argument is worth making explicit. Any coherent atlas is a bijective recoding of the true whole product, because the pair supports describe precisely equality of shared true coordinates and global support is full. At a fixed old history, the transported true transition log-density is a sum of functions supported on observation patches: each original atom is recoverable in some patch. The candidate product kernel also has patch-supported log-density. If all full next-patch marginals agree, then the expectation of their log-density ratio agrees under both distributions. Its difference is the sum of the two directed KL divergences, so both vanish. Therefore the whole transitions agree, even for cyclic observation covers. This is not the false claim that arbitrary distributions are determined by pair marginals.

This gives a sound-and-complete family of patch-compatible product realizations of the same process, up to labels. It excludes invisible extra states, arbitrary hidden extensions, non-product supports, and observation grammars that do not make each elementary factor available in any patch. Its factor-count and resource choices need not be unique. Parent scopes and deterministic interface quotients can be computed for each retained local chart assignment, and used as additional admissibility constraints.

Representing this family without enumerating all global chart assignments needs an additional complexity condition. The gluing note constructs a finite constraint representation. With bounded observation-overlap width and bounded width of the actual combined chart, temporal-context and interface constraint graph, standard tree-decomposition dynamic programming yields a compact solution DAG and polynomial work in the number of patches for fixed widths and local alphabets. The solution family can still have exponentially many members. Without the width promise, local calibration and local chart construction remain bounded-width computations, but global compatibility search has no polynomial guarantee.

This unresolved-family theorem is often the more faithful statement of the target. The generic product-separation theorem identifies a unique finest elementary atlas when evidence supports it; the family theorem retains genuine alternatives when it does not.

## 11. Main population theorem

Under the model and observation assumptions of Section1, positive local kernels, and either dynamic richness or the weaker product-separation condition of every patch's sufficient conditional next-state row family, the construction in Sections2–6 identifies the finest admissible elementary finite-state coordinate system of the conditional transition row families, patch ownership, sensor mechanisms, essential delayed parent sets and positive local update kernels, up to coordinate permutation and independent state relabeling. It uses polynomially many bounded-patch history laws and local computations when R,w,d,L and observation alphabet bounds are fixed, and never enumerates the global hidden product state space.

For every bounded candidate region, Section7 constructs the smallest deterministic autonomous boundary-state quotient compatible with the specified outgoing receivers and incoming interface values. Section8 distinguishes exact coupled witnesses from insufficient marginal summaries and supplies bounded-scope tests for joint crossing-summary realization. These latter conclusions hold for all initial states under the same boundary contract; stationary access is used for identification, not as a substitute for all-state algebraic verification.

This is a structured-subclass discovery theorem, not a general solution to partially observed network identification. The three-view calibration, product-rigidity, bounded-parent selection and partition-refinement mechanisms each have established precedents. The substantive research burden is their sound composition with unsupplied local state alphabets, nonlinear delayed interactions, recursively maintained interfaces, and joint witness preservation.
