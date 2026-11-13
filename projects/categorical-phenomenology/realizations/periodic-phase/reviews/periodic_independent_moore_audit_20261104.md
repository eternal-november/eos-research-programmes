# Independent mathematical audit: observable periodic-phase theorem

## Result

The intended periodic extension is mathematically sound. The stochastic convention must explicitly require a nonnegative initial probability row and continuous outcome matrices. This omission was detected in draft 7aef1706ec629fd9df6bd5348014a95ddd1b90750bfefe10b5b29c2bb836866a and has been corrected by the author. The final frozen manuscript is approved: SHA256 1098741a19d81f52f1371eed6b0a391b9f65e3302f7ba11e0409452b5af1eab3. Its exact delta from the fully inspected snapshot 100d35a3ebcf50387081feb77843b56f49f589108eb43385bbdc21a541eabf52 was checked: the lmodern font package and a dimensional/finite-width corollary. That added corollary also checks: Hom-complex connectivity gives p+q over finite q-dimensional CW bases, the permutation-matrix fiber gives width p exactly for globally labelable phase covers, and finite trivializing charts plus a partition of unity give finite width on compact Hausdorff bases. No remaining mathematical blocker was found. This is a mathematical review, not formal verification or novelty certification.

## Detailed checks

1. Residue permutation symmetry at full-cycle horizons suffices. Shorter cylinder laws and arbitrary finite within-residue permutations follow by extending to a sufficiently long full-cycle cylinder and summing unused coordinates. The empirical-measure construction gives a unique profile measure on Delta(Y)^m. Every mixed coordinate monomial is a marginal of such a cylinder. This makes the representation and weak continuity valid without stationarity.

2. Aligned block rank counts initial profile atoms, not all one-step phases. The map from a profile to its product block law is injective by taking marginals, so the aligned block Hankel is a polynomial moment Gram kernel with rank equal to initial support size. It is a submatrix of the ordinary Hankel and therefore has finite rank at most p.

3. Ordinary rank equals the number of distinct profiles in the rotation closure. Finite prefix classifiers recover each positive initial atom's phase law as a pointwise limit of reachable continuations. The ordinary predictive row space has finite dimension and is closed in the pointwise topology: a finite set of evaluation coordinates supplies an invertible coordinate system. Each positive symbol shift then recovers the rotated phase. Long profile classifiers make all distinct phase laws linearly independent. Every reachable continuation lies in their span, giving equality in both directions.

4. Averaging over the first m shift offsets is valid even when initial phase weights vanish. The averaged directing measure has exactly p strictly positive atoms, so local isolating bumps recover the full phase cover and both original and averaged weights continuously. Constant ordinary rank and compactness give positive uniform separation and averaged weight bounds. Original support size need not be constant.

5. One-step shift orientation is correct. With Pi_{a,tau(a)}=1, the symbol matrix is M_y=D_y Pi. It emits from the current phase and then advances to the next one. The word product telescopes into the prescribed periodic independent law.

6. Arbitrary-native extraction does not use hidden stationarity. The row bar-rho=(1/m)sum_{r=0}^{m-1}rho T^r realizes the observable average at unchanged width. It need not be a stationary hidden distribution. Two adjacent blocks of length n=mt are conditionally independent and return to the same profile, giving J=C^T diag(bar-w) C. The classifier, positivity, exact repair, and signed embedding proofs from the held-IID case therefore carry over without modification.

7. The displayed constants check. There are md empirical coordinates with t independent samples each; Hoeffding at radius delta/8 gives 2md exp(-t delta^2/32). The stated t makes this at most bar-w*/8. Thus diagonal QL is at least 6/7 and the stochastic repair denominator is at least 3/28. The signed classifier matrix satisfies ||C-I||_infinity <= 2 epsilon < 1.

8. Dynamic lifting needs no extra equivariance condition on the encoder. An arbitrary equivariant split QL=I lifts the canonical permutation using T=L Pi Q, with rho=wQ and N_y=L D_y Pi Q. Native transitions are allowed to be stochastic, not required to permute native slots. This scope distinction is necessary and is explicitly retained.

9. Both ordinary HMM conventions are correct. For emission then transition, e_y=L d_y gives Q diag(e_y)=D_y Q and Q diag(e_y)T=D_y Pi Q. For transition then emission, tilde-D_y=Pi^{-1}D_y Pi is required; then T diag(L tilde-D_y 1)=L Pi tilde-D_y Q=L D_y Pi Q. Reusing the unshifted emission vector in the second convention would generally be wrong; the manuscript uses the correct shifted one.

10. The signed lower bound is valid for arbitrary nonminimal signed competitors. Averaging preserves terminal normalization. The matrix B=(C^T diag(bar-w))^{-1}R satisfies B1=1 and BL=C, hence has row rank p and equivariantly embeds the centered bundle into 1_k^perp. A centered-bundle embedding supplies the normalized signed upper split as before.

11. Robustness needs horizon H=2n+m-1 for a general nonstationary target. Each offset-r two-block window is a marginal of that horizon. Total variation contracts under marginalization and averaging, supplying the averaged two-block bound. The target diagonal margin is at least 3bar-w*/32; its perturbation is at most 7beta/4 <=7bar-w*/256. For a stationary target, its law already equals the average and H=2n suffices, even if the competing hidden model is not stationary.

12. The stationary aligned-block strengthening is correct independently of finite rank. Given a directing block law q, one-site-shifted blocks have empirical law F(q)=q_tail tensor q_first; their even and odd subsequences are each conditionally IID because they use disjoint pairs of original blocks. Stationarity implies lambda=F_*lambda. Iterating F m times produces the product of all coordinate marginals, forcing product atoms. Rotation invariance follows on this product locus. This proves residue-wise exchangeability and equality of ordinary and block ranks in the finite-atomic case.

13. The temporal Moore example is genuinely nonexchangeable. The three emission rows are linearly independent since they are affinely independent probability vectors. Its pair table is V^T Pi V/3. Symmetry would imply Pi=Pi^T after multiplying by a right inverse of V on both sides, impossible for a three-cycle. This holds at every parameter value. The phase cover and centered plane bundle are the same ones as in the independently checked held-IID example, so local/signed/stochastic widths are 3/4/5; normalization remains essential to the signed width 4.

14. The two failure examples are valid. Alternating independent Bernoulli parameters a!=b have aligned block rank 1 but ordinary rank 2. IID repeated-bit pairs have a nonproduct block atom and violate independent residue permutations. They have ordinary rank exactly 3: the three-state boundary/memory-0/memory-1 model gives the upper bound, while rows (empty,0,1) and columns (empty,0,00) give the Hankel minor [[1,1/2,1/2],[1/2,1/2,1/4],[1/2,0,0]], determinant -1/16.

## Source and scope checks

Carl Graham, Convergence of multi-class systems of fixed possibly infinite sizes, arXiv:0902.0539, Theorem 3, directly supports conditional independence between infinite residue classes given their directing-measure vector. The primary PDF also attributes the all-infinite case to Aldous, Corollary 3.9. This supports the representation ingredient, not a novelty claim for the topological-width theorem. Primary PDF checked: https://arxiv.org/pdf/0902.0539 .

No extension to general nonexchangeable HMM families follows. The symmetry/finite-phase decomposition is essential. The separate probability-clock scope sentence matches the interval theorem in the supplied Positive_Dynamics_Obstruction.tex, which has its own independent source audit. That companion is not used by any periodic theorem proof above and was not fully re-audited in this pass.
