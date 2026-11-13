# Independent mathematical review: finite cover recovery

## Status

The manuscript has been reviewed in full. The main algorithm, deterministic matching lemma, probability bounds, period extension, width corollary, corruption guarantee, and testing lower bounds are valid under their stated promises. Two feasible-parameter restrictions were requested in the unsampled-arc construction: 0<delta<=sqrt(2)/8 and L>0. The author applied both. Final frozen source approved: SHA256 137724f0f1c29d3a84180513282ead25567df6281a564ff6b4424c37f59132d2. Exact delta from the fully reviewed source 95b14fedd7e8cd3bf82cd4f3ec18fb999e2eb7a00dfd3920a117e569f791c16a is only the heading correction from “initial zero weights require randomized offsets” to “randomized offsets reveal initially absent phases”. This avoids claiming randomization is necessary when deterministic allocation over offsets is also possible. Mathematical statements and proofs are unchanged, and no remaining mathematical blocker was found.

This is an independent mathematical audit, not formal verification or a novelty certification.

## 1. Statistical constants

For r=delta/8, conditional Hoeffding gives 2d exp(-2nr^2)=2d exp(-n delta^2/32) per trajectory. The stated n therefore makes the union bound over all VN trajectories at most alpha/2. The stated N makes Vp exp(-Nw0)<=alpha/2. Independence of restarts is needed for the missing-component probability; no independence between the two good events is assumed or needed.

On their intersection, same-atom empirical vectors have distance <=delta/4 and different-atom vectors have distance >=3delta/4. Thus the graph threshold delta/2 identifies the latent classes exactly, with no chaining ambiguity. Convex averaging preserves the r atom-error bound. The mesh condition gives Lh+2r<=3delta/8<delta/2.

The unknown-p variant is valid because the positive-mass promise implies p<=floor(1/w0). It does not estimate the mass bound or certify absence of smaller-weight components outside the promised class. The ceilings, logarithms, total symbol counts, and uniform-mesh V=max(3,ceil(8L ell/delta)) are consistent. In the nontrivial rotating-pair example, V=18 indeed gives pi/18<sqrt(2)/8 after canceling the radius a.

## 2. Matching, closing the circle, and conjugacy

Let G_i denote true continuation along the ith oriented mesh arc. The good-data matching is exactly T_i=lambda_{i+1}^{-1} G_i lambda_i. At the closing edge, lambda_V is the same lambda_0 used at the starting vertex. Consequently their product is lambda_0^{-1}(G_{V-1}...G_0)lambda_0. This proves conjugacy to the circle generator's actual monodromy, not merely parity or a subgroup invariant.

The wrong-match lower bound is delta-Lh-2r>delta/2 and the true-match upper bound is Lh+2r<delta/2, so strict thresholding handles equality cases in the empirical error bounds correctly. Every relation is a bijection because it is the true continuation map in local coordinates. The circle and orientation are supplied; no unknown-base topology recovery is claimed.

A finite covering of a circle is classified by this generator permutation up to conjugacy. Therefore the resulting cover-isomorphism statement is correct. The identity and sign tests in the width corollary are conjugacy invariant. That corollary correctly treats the earlier arbitrary-native classification as an input, rather than inferring width from finite vertex fitting alone.

## 3. Other local estimators and corruption

The transportation lemma is valid. If an estimated measure has no support point in the open r-ball around one true atom, every coupling must transport that atom's mass at least distance r, costing at least w0 r. Disjointness of the p balls, together with at most p estimated support points, gives exactly one point per ball and a unique matching. Strict transportation error supplies the needed strict paired distance.

The bounded-corruption length formula is correct: concentration radius delta/8-eta plus deterministic report error eta gives total error delta/8. Changing an eta fraction of symbols in a held-IID trajectory changes every empirical coordinate by at most eta, even if changes are adversarial. For a periodic extension of this corruption observation, the bound must apply to each residue-frequency coordinate; corruption of an eta fraction of all mt symbols can concentrate in one residue and produce error m eta. This is a clarification of scope, not a defect in the held-IID statement.

## 4. Periodic extension

Conditional on the original profile S and the independently selected offset U, the retained trajectory has periodic-product profile R^U S. Averaging over U gives exactly the stated rotation-averaged measure, including repeated profiles from shorter rotation orbits. Independence of restarts and offsets yields independent retained profile draws. Initial weights may vanish; the positive bound is needed on averaged weights, exactly as stated.

Each of the md profile coordinates is estimated from t independent Bernoulli variables, so the modified concentration bound and all preceding clustering/coverage constants carry over with d replaced by md and n by t. Observed-symbol count includes the discarded prefix and is at most VN(mt+m-1).

Rotation is an isometry. Correct phase-advance matches have distance <=2r=delta/4 and incorrect ones >=delta-2r=3delta/4, proving recovery of tau. The compatibility relation is T_i tau_i=tau_{i+1} T_i, not an unexplained same-fiber commutation. The manuscript now states this explicitly. No latent-phase intervention is used.

## 5. Lower bounds

### Unsampled arcs

The rotating pair is always positive for a<=1/8 and has separation 2a max(|cos phi|,|sin phi|)>=sqrt(2)a. Its endpoint unordered fibers coincide after a half turn, but its monodromy exchanges the two sheets. Hiding this motion in an unqueried complementary arc therefore gives identical full word laws at all prescribed query points and different covers. Smooth flat-endpoint interpolation is available when no numerical modulus is imposed.

For the Lipschitz version, linear rotation over an arc of length g has lifted speed at most a pi/g. Setting a=delta/sqrt(2), with the now-explicit feasible range 0<delta<=sqrt(2)/8 and L>0, gives the stated gap threshold. This is a lower bound for prescribed designs, not an adaptive-query lower bound; that distinction is correctly stated.

### Rare-sheet coupling

The common atom has probability 1-2w under both hypotheses. Couple the random seed and all latent common/rare choices. On the event that S padded choices are common, all observed symbols are five, both adaptive designs follow identical histories, and both transcripts coincide. Its probability is (1-2w)^S, giving transcript overlap at least that amount and minimax error at least half that amount. Early stopping does not invalidate this padding argument. Arbitrarily long individual trajectories do not remove this error floor.

### Symbol-budget KL

The rare coordinates remain at least 1/8. For corresponding rare atom distributions, squared Euclidean difference is 4a^2(1-cos(phi))<=8a^2. The chi-square upper bound on KL therefore gives KL<=64a^2=32delta^2. Adding the latent label makes a length-q trajectory's KL at most 2w q (32delta^2); hiding it can only decrease KL.

Adaptive parameters and lengths have the same conditional design kernel at any shared past transcript. Applying the KL chain rule to the finite sequence of experiments, then the almost-sure total-symbol bound, gives transcript KL<=64w delta^2 B. The equal-prior error lower bound (1/4)exp(-KL) follows from the displayed Hellinger/Jensen/Cauchy-Schwarz calculation. Both topologies are distinct conjugacy classes, so a successful monodromy estimator yields the required binary test. The logarithmic lower-bound rearrangements and their stated positivity qualifications are correct.

These arguments do not establish a vertexwise coupon-collector lower bound, an unavoidable product of all upper-bound factors, or optimal trajectory length. The manuscript appropriately avoids those claims.

## 6. Prior art and scope

Fan and Li, Efficient Algorithms for Sparse Moment Problems without Separation, COLT 2023, Appendix F Lemma 49, was checked in the primary PMLR PDF. It states the categorical p-component transportation recovery guarantee quoted in the manuscript: constant success probability, (2p-1)-snapshots, and (pd/epsilon)^{O(p)} samples. The source also treats refined dimension dependence. Thus the local-learning comparison is accurate; it is not a new statistical-mixture estimator claim. Primary source: https://proceedings.mlr.press/v195/fan23b/fan23b.pdf .

The overall upper bound composes concentration and component coverage with an elementary deterministic matching argument and the already established native-width theorem. The finite-data guarantee remains conditional on exact structure, restart access, separation, lower masses, and known regularity. It does not validate those promises from observations. In particular, finite target samples do not rule out an unrestricted highly oscillatory lower-width competitor fitting those samples.
