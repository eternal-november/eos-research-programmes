# Cheap observable validation of a proposed hidden decomposition

28 October 2026. A class-relative proposal/check theorem for `Coupled_Family.md`, separate from general black-box latent-model validation.

## Assumptions and output

Use the stationary subclass with invertible terminal lag matrix. Its full hidden lag vector is uniform on F2^(nL); exploration actions are independently uniform. True M has unknown invertible blocks of size <=q, innovation biases alpha_i=1-2p_i lie in [alpha_min,alpha_max] subset (0,1), and raw recurrence rows have at most r terms. Observations have calibrated independent binary noise with sign bias gamma>0.

A proposal supplies raw recurrence C_hat,F_hat with the same row-width bound and an invertible proposed mixing M_hat with blocks of size <=q. The verifier does not search for these objects. It validates their deterministic form and then estimates O(n^2) bounded-width observable parity moments. Subject to the declared model class and simultaneous confidence, acceptance certifies the exact raw recurrence and M_hat=M Pi for a latent-coordinate permutation Pi; it also provides confidence intervals for innovation probabilities. It does not certify that the world belongs to this family.

## 1. One moment per proposed recurrence row

Let R_i be the proposed raw residual W_ti + C_hat_i history + F_hat_i U_t. If the row is correct, R_i=Z_ti and

    E(-1)^R_i >= alpha_min^q.

If it is wrong, R_i is Z_ti plus a nonzero parity of the uniformly distributed raw lag history and independent action. Thus its expectation is **exactly zero**. Current Z is independent of that history/action. This is stronger than the general-history regression gap and is specific to the uniform stationary subclass.

Estimate the corresponding corrected observable parity mean and accept the row only if it exceeds alpha_min^q/2. With error <=alpha_min^q/4, every correct row passes and every wrong row fails. There is no competitor enumeration. The raw action and recurrence coefficients are validated together.

## 2. Pairwise innovation tests certify the proposed frame within this class

After recurrence validation, define the proposed innovation vector formally by

    E' = M_hat^(-1) Z = Q E,       Q=M_hat^(-1)M.

This is not an observed sample; its characteristic moments are computed from corrected readout-window parities. Each row of Q has at most q^2 nonzeros: a proposed inverse row combines <=q raw rows, each of which combines <=q true innovations. Q is invertible.

For distinct rows i,j, let S_i,S_j be their innovation supports. Their sign covariance is

    Cov((-1)^E'_i,(-1)^E'_j)
      = product_{k in S_i symmetric_difference S_j} alpha_k
        * (1-product_{k in S_i intersection S_j} alpha_k^2).

It is zero exactly when the supports are disjoint, and is strictly positive otherwise. A uniform positive lower bound for a nonzero covariance is

    Delta = alpha_min^(2q^2) (alpha_max^(-2)-1).

Equivalently this follows by dividing the joint characteristic by the product of means; no cancellation occurs because all alpha are strictly between zero and one. Since Q is invertible, its n rows have nonempty supports. If all pairwise covariances vanish, n nonempty pairwise-disjoint supports within n columns must each be a singleton. Hence Q is a permutation matrix. Consequently M_hat is the true frame up to column permutation. Equal biases do not introduce extra linear ambiguity.

The implication “pairwise independence implies independent latent coordinates” is **not** claimed for arbitrary distributions. It holds here because the candidate variables are invertible linear combinations of the stipulated independent strictly biased innovations. Affine sign flips and negative biases are excluded by this family; allowing them requires a corresponding signed/affine gauge statement.

Estimate each mean and each pair-characteristic within epsilon. Covariance error is at most 3epsilon+epsilon^2. For epsilon<=min(1,Delta/8), this is <=Delta/2. A strict threshold between the error band and the true-gap band (or epsilon<Delta/8 and threshold Delta/2) separates zeros from nonzeros. Correct proposals pass and all wrong frames fail on that simultaneous event. Boundary equality can be avoided by choosing epsilon<=Delta/16.

## 3. Observable width, sample accounting, and post-selection

One proposed transformed-innovation coordinate uses at most q raw recurrence rows, hence <=q(r+1) observed locations. A pair uses at most

    w_val=2q(r+1)

locations, with repeated locations canceled modulo two. The observation correction multiplies by at most gamma^(-w_val). All action characters involve only the fixed a current-action bits.

For a proposal fixed independently of a validation trajectory, there are n recurrence moments, n proposed innovation means, and n(n-1)/2 pair moments. Evaluation uses O(n^2) such moments, with cost proportional to sample count times their bounded widths. Sample bounds use the explicit N/g schedule of `Coupled_Family.md` with B_obs=gamma^(-w_val), the appropriate moment count, and either contraction or the invertible-companion Fourier mixing bound.

For a data-selected proposal using the same trajectory, cover *all* possible width-w_val observable parities and action subsets in the confidence event:

    K <= 2^a sum_{j<=w_val} binomial(n(L+1),j).

Only the proposed O(n^2) moments need be evaluated, while the confidence proof union-bounds the larger class. This log K costs only O(w_val log n) in sample size at fixed widths. Alternatively use an independent stationary validation trajectory. One must not pretend a later segment of the same run is independent without charging an appropriate mixing gap.

Once Q is certified a permutation, the proposed innovation means estimate alpha_i directly and p_i=(1-alpha_i)/2. Error epsilon in those means gives p error at most epsilon/2. The usual nH epsilon_p transcript-TV bound then applies to a fitted model initialized with the common uniform lag law, uniformly over observable-history policies.

## 4. What the proposal/check separation establishes

The discovery algorithm enumerates up to n(nL+a)^{O(r)} candidate recurrence rows and subsequently recovers the mixing. The verifier checks a supplied proposal with O(n^2) bounded-width empirical moments and polynomial local algebra, without repeating that candidate search and without enumerating 2^(nL) states. This is a concrete search-versus-certificate-work separation relative to the supplied algorithm, not an information-theoretic lower bound on every alternative learner. It is most useful when many candidate models or changed decompositions are proposed, or when a fitted architecture is passed to a separate checker.

After observable validation, learned region support and persistent-interface certificates are checked algebraically as in `Discovery_Calculus_Bridge.md`. This joins cheap observable class-relative validation to original-calculus local refinement/reuse. Standard finite-field independence identities, sparse residual testing and linear-circuit checking are the mechanisms; no claim is made that those ingredients are new.

## Deployment and scope clarification

The finite-horizon comparison requires matched deployment initial laws, including after conditioning on training data when a controller is data-selected. A fresh independent common-uniform start is sufficient. Same-run continuation is not automatically a common-uniform start. A certified initial-law TV discrepancy epsilon_0 adds to the innovation mismatch bound, giving min(1, epsilon_0+nH epsilon_p). Physical hazard transfer requires a sound event interpretation or conservative proxy relation; class-relative confidence does not certify the physical world belongs to the class. See `Audit_Scope_Clarifications.md`. The canonical mixing target is the finest indecomposable partition, not an arbitrary assigned coarsening.
