# Independent algorithm and counterexample audit

Reviewed source SHA256:
`137724f0f1c29d3a84180513282ead25567df6281a564ff6b4424c37f59132d2`

Final-version approval: the preceding reviewed version had hash `95b14fedd7e8cd3bf82cd4f3ec18fb999e2eb7a00dfd3920a117e569f791c16a`. Its only reported source change was the periodic-section heading, now “Periodic extension: randomized offsets reveal initially absent phases.” This appropriately avoids suggesting randomized offsets are the only possible access strategy. The final heading and hash were verified, and the check script was rerun successfully against the final source. The mathematical assessment below is unchanged.

## Result

No substantive mathematical error or counterexample satisfying all stated hypotheses was found. The finite checks pass. The scripts are evidence about implementations, constants, and examples, not replacements for the manuscript's proofs.

## Deterministic and concentration steps

The matching argument uses the correct two-sided estimation allowance: a true edge is at distance at most Lh+2r, whereas every wrong edge is at least delta-Lh-2r. The strict hypothesis separates both sides of the delta/2 threshold. At r=delta/8 and Lh<=delta/8, the promised margin is strict.

The within-vertex graph cannot chain distinct true atoms on the good event: same-atom distances are at most delta/4 and different-atom distances are at least 3delta/4. The cluster mean stays within the same coordinatewise radius by convexity. A union bound needs no independence between coordinates or vertices; the stronger independence promises are sufficient.

The N formula bounds missing components by alpha/2. The n formula uses 2nr^2=n delta^2/32 and bounds all trajectory-coordinate deviations by alpha/2. The unknown-p replacement by floor(1/w0) is legitimate because p w0<=1. The tested ceiling formulas satisfy both inequalities numerically with strict slack.

## Periodic extension

Discarding U initial outputs applies R^U to the profile, not its inverse. Uniform independent U therefore samples the rotation-averaged directing law. The effective samples remain independent across restarts. Each residue coordinate still has t independent Bernoulli trials conditional on the effective profile; dependence between coordinates does not invalidate the coordinate union bound.

Rotation is an isometry, giving a same-vertex phase-advance matching margin of 2r=delta/4. The correct cross-vertex compatibility is T_i tau_i=tau_(i+1) T_i, rather than literal commutation of permutations expressed in unrelated vertex labels. The manuscript now states this indexed identity explicitly.

The test fixture's initial weights are genuinely continuous on the nontrivial cover, with a zero at one vertex and uniformly positive rotation average. A globally fixed single visible phase would not be a valid continuous-weight fixture on this connected three-sheet cover. The test avoids that pitfall.

## Robustness and transport

Bounded corruption consumes an additive eta from the empirical error budget, yielding the stated exponent 2n(delta/8-eta)^2. It does not silently tolerate an arbitrary proportion of completely corrupted trajectories.

The transportation lemma's open-ball argument is valid with at most p estimated support points. Both strictness and the support-size condition are necessary for its exact conclusion; explicit negative controls are included.

## Lower bounds

The unsampled-arc half-twist distinguishes different monodromies while preserving all sampled word laws. The amended parameter range guarantees positivity and feasibility of the chosen amplitude, and L>0 is needed for the displayed gap formula. The claim is appropriately limited to prescribed finite designs rather than general adaptive lower bounds.

The rare-sheet coupling gives a common transcript event of probability at least (1-2w)^S even with early stopping, by padding latent choices. For the KL argument, corresponding rare categorical probabilities are at least 1/8. Their squared Euclidean difference is at most 8a^2, giving KL<=64a^2=32delta^2 per rare draw and the stated 64wdelta^2 per observed symbol after weighting both rare labels. The predictable experiment-length restriction makes the trajectory-level conditional KL chain rule directly applicable. These mathematical steps were reviewed; the numerical grid only sanity-checks constants.

## Scope retained

The recovery theorem is conditional on exact model structure, positive mass and separation bounds, known parameter access, and a known continuation modulus. The controls show why finite successful vertex matching cannot certify these promises or rule out an unseen twist. The circle width decision relies on the imported arbitrary-native classification. This audit does not independently prove that classification or establish novelty.
