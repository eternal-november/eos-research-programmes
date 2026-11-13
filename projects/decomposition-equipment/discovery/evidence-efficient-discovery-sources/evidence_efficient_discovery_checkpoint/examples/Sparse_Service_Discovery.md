# Evidence-efficient discovery of a recurrent interacting predictive decomposition

## Plain-language abstract

The learner sees repeated action/readout records, not the equations used to generate them. It discovers that each of two readout channels needs its own previous reading, the other channel's current reading, and its own action. It also discovers that the channels' next readings cannot be forecast independently. These findings compile into two tiny recurrent predictors with an explicit shared random source.

We then test the learned predictor on fresh records collected under four feedback controllers. With fewer than 100,000 total simulated episodes, the certificate bounds the prediction error for every question depending on any three readout bits across an eight-step run. It does not merely check one hand-picked safety event. Several deliberately simplified predictors fail this same test.

This is a narrower promise than the preceding report's guarantee for every complete trajectory and every controller. The reduction in data comes from explicitly choosing the observations and controllers that the certificate must support—not from proving that the earlier broad guarantee is cheap. We do not assume that the real environment belongs to the learned model class. Nor do we conclude that the learned components are unique physical mechanisms. This is a positive, reusable, evidence-efficient predictive discovery result within a declared operational scope.

## Acquisition and target

Two binary readout ports are supplied. Their needed predictive inputs are not supplied. We acquire:

* 10,000 training episodes with independently uniform joint actions;
* 20,000 independent held-out episodes for each of four feedback controllers;
* eight transitions per episode, with an initial two-readout history.

Thus the run uses 90,000 episodes and 720,000 transitions. The predecessor used 10,240,000 episodes of two transitions: 113.78 times as many episodes, or 28.44 times as many observed transitions. This is **not** a like-for-like improvement on its full-trajectory, all-controller guarantee.

The controller family is fixed: request when clear, request when busy, use the other channel's current reading with an asymmetric complement, and respond to the change between one's previous and current reading. No independence of the two controllers' state is assumed. Each deployment selects one of these policies at the beginning. Arbitrarily switching policies during a run is outside the certificate.

The operational questions are all bounded functions of any three of the 18 binary readings available from time zero through time eight. There are 816 three-bit projections. Each projection has eight outcomes; certifying its total variation certifies every bounded score and every Boolean event on that projection. This includes joint cross-channel and nonadjacent-time questions. It does not include an unrestricted event depending on four or more readings.

## Actual discovery, not supplied factorization

The training learner considers all 64 subsets of the six possible one-step predictive inputs `(current0,current1,previous0,previous1,action0,action1)` for each port. It scores the corresponding fitted Bernoulli tables by BIC. The finite-memory search bound and the two output ports are part of the proposal language, not a promise about the physical law.

It selects `(current1,previous0,action0)` and `(current0,previous1,action1)`. The local probability tables are learned, then rounded to tenths as a proposal heuristic. A least-squares estimate of the common-versus-independent threshold mixture is 0.4969034; its proposed rounded value is one half. The initial law is also proposed from training counts. None of these rounding decisions is trusted by the confidence theorem.

The candidate is frozen before hold-out generation. Its positive implementation uses one local memory bit and the current neighboring bit at each port, with a shared threshold driver of the same explicit kind as the previous report. A shared driver is a predictor resource, not a discovered physical noise mechanism. The local updates recursively store the current local readout; there is no access to an uncharged full history. The shared source must be distributed or jointly evaluated, and its resource cost is not zero.

The synthetic generator has genuine delayed dependence on one's own past and on the neighboring channel, with positively correlated next-step noise. It has no reset that exposes the discovered scope. Nevertheless it remains the deliberately simple service family used in the predecessor. This is a controlled comparison, not a validation on unfamiliar hardware.

## Independent exact certificate

For each controller and projection, let the empirical eight-outcome law be p-hat and the candidate's exact projected law be q. The candidate probabilities are calculated by integer dynamic programming, not Monte Carlo. For N=20,000, the multinomial bound gives

    Pr(TV(p-hat,p)>r) <= (2^8-2) exp(-2 N r^2).

Use the fixed radius r=41/2000=.0205. A union bound over four controllers and 816 projections has failure probability less than .041505. The checker certifies this inequality by rational arithmetic using a finite Taylor lower bound for exp(16.81), not a floating logarithm. Independence between different projections is not required. Independence and common law of repeated episodes under each tested controller are required.

The largest observed projection discrepancy is .017762112578125, under the crossed controller. Therefore, simultaneously for all declared controllers and projections,

    TV(true projection, learned projection) <= .038262112578125 < .05

with confidence at least .9584956. On this one event, every bounded [0,1] score of any such projection transfers with the same additive error. Candidate selection does not incur an additional search penalty because the confidence statement uniformly controls the empirical projections and the predictor is separately frozen.

The confidence theorem does not assume a Markov truth, the selected scopes, a shared noise generator, a latent state size, or the synthetic generator's equations. An out-of-class physical law that passes the observations is still only guaranteed to match these operational tests. Undetected higher-order dependence is not excluded.

## Resource ablations and what they establish

Three fixed simpler predictors are checked: averaging away own previous readout, averaging away the neighboring message, and retaining the local laws while replacing the shared source by independent updates. Exact projected separations from the learned candidate are respectively .10, .144, and .155. The same hold-out event also produces lower bounds exceeding .05 for all three simpler predictors. Thus these are actual failed alternatives under the declared operational criterion, not a narrative claim that coupling must matter.

They do **not** prove that every memoryless, message-free, or differently coordinated implementation fails. Relocation of memory, richer messages, altered controller access, a different latent realization, or another proposal language may change the resource tradeoff. The BIC result is a learned program, not a global resource optimum or an identification theorem for physical components.

## Limits and acceptance criteria

The result succeeds at discovering and independently certifying one explicit, recurrent, positive, interacting predictor at a substantially smaller evidence budget for a useful but restricted query language. It does not solve generic architecture discovery, physical hazard grounding, universally safe exploration, unbounded-horizon certification, or unmeasured-controller transfer. The eight-step holdout policies might themselves be unsafe on actual hardware; their availability is an acquisition assumption.

The mathematics supporting the confidence step is standard multinomial concentration. The constructive contribution of this bounded experiment is that actual unknown scope/source proposals, recursive compilation, exact projected prediction, independent operational certification, and informative failed alternatives fit together without a truth-model promise. Claims of a novel concentration or identification theorem would be inappropriate.

The source script writes the training data, frozen candidate, heldout projection histograms, exact candidate projection probabilities, rational confidence calculation, and reproducible result JSON. The reported bounds concern the supplied synthetic counts; NumPy's pseudorandom generation is not physical experimentation or machine-checked mathematics.
