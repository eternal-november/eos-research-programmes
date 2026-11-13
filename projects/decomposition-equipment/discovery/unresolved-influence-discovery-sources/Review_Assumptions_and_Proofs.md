# Independent review of discovery under unresolved influences

Status: accepted under the explicit scope and assumptions below, 29 October 2026. This is an AI mathematical/code review, not human peer review or proof-assistant verification.

## Main moment-completion theorem

The proof in main/Readout_Moment_Discovery.md is sound under its stated controlled-Markov observed-state and exact conditional-moment universe. In particular:

- Gram regression recovers the declared bounded-degree conditional moment functions without a supplied state partition, provided the degree promise and positive-definite Gram condition hold.
- A function outside the measured feature span admits a signed outcome perturbation annihilating all measured moments and normalization. Strict positivity of a compatible kernel permits a sufficiently small perturbation.
- Any proper quotient identifies two old states. Perturbing their rows unequally destroys closure for an unmeasured block indicator. Thus every proper universally valid quotient algebra must be contained in the measured span.
- Transition invariance AND pointwise multiplication closure are required. A mere invariant linear span does not certify the joint distribution of several component coordinates.
- Iterating algebra generation and learned transition images yields the coarsest proper universally valid task quotient, or an obstruction to every proper quotient in this particular maximal completion family. This is not a claim for arbitrary smaller parameter-coupled universes.
- The stationary one-action extension correctly balances two row perturbations by their stationary masses. It preserves the common stationary law and all measured one-step moments, not all longer trajectory laws.

The arithmetic bound must charge the given task representation, maintained polynomial support, coefficient encoding, and exact algebraic-number operations. A task with a compact expression can still generate a large block-indicator algebra. Fixed moment degrees make the dictionary polynomial in the observed coordinate count, but do not yield a generic small-state or small-certificate theorem when degrees grow.

## Obstruction and experiment certificates

The compact-polytope LP criteria in obstructions/Obstruction_and_Experiment_Certificates.md are sound. They distinguish uniform quotient validity, existence of valid and invalid worlds, uniform invalidity of one candidate, and identification of the reduced kernel. The actual affine hull of the feasible polytope is essential when inequalities force a face. The experiment nullspace condition is correct for identifying linear functionals; the note appropriately avoids claiming it is always necessary for a Boolean validity decision.

The four-state example has identical entire passive observed histories across its fixed parameter family, despite different pointwise dependence on the unobserved bit. The conditional refresh ordering makes the hidden bit independent of the observed history at each step. This is a useful warning that a Markov predictor does not certify physical autonomy under changes to hidden mechanisms.

The supplied obstruction checker was independently rerun successfully. It checks exact rational words through length ten, positivity, pointwise contrasts, coupled parameter extrema, the affine-hull face case, and the experiment nullspace calculation. These bounded checks supplement the proofs and are not their replacement.

## Crucial boundary for the positive family

A growing parity family with known independent output-bit noise and extremal deconvolved moments belongs to a smaller structural universe than arbitrary moment completion. Its parity constraints can certify high-order joint behavior because they force pre-noise outputs onto a deterministic parity support, followed by known independent noise on disjoint pairs. This is a separate argument, not an instance of the maximal moment-completion theorem at fixed degree.

Exact saturation identifies hidden behavior only on the support represented by the observations. Approximate saturation controls average mismatch; without hidden-mode mass or distribution-shift restrictions it does not supply a pointwise guarantee for rare or new hidden modes. An observed-state Markov assumption repairs the mathematical world definition but narrows the interpretation to a stochastic factor of that observed process. It must not be presented as identification of a physically autonomous subsystem under arbitrary changes to an unobserved environment.

Independent bit-flip noise can provide polynomial conditioning of a fixed-degree Walsh dictionary without a lower bound on every whole-state probability. This requires the noise to be genuinely independent in the stated timing. It is not supplied by merely seeing noisy data. The written family and its code were subsequently reviewed and rerun successfully, as recorded below.

## Additional main-theorem checks

The added resolution bound |Q|<=2^d is correct: each nonempty quotient block has a nonzero degree-at-most-d indicator, hence at least 2^(n-d) support points. The support bound follows by induction on a multilinear polynomial's last variable. This applies only to the maximal strictly positive moment-completion universe; extra structural laws can evade it.

The new nonextremal four-state-core construction is valid. The learned task image reveals an unknown two-coordinate parity; its product with the task closes the four-dimensional observable algebra. The three operator identities follow from independent output flips on the three distinct raw coordinates. The learner need not know the noise parameter for this example. It discovers a functional component, not the residual physical source law. The observation-side low-degree promise and informative design remain substantial assumptions.

The exact rational main/check_moment_discovery.py was independently inspected and rerun successfully. Sparse Walsh closure is the primary calculation; small whole-state tables independently validate positivity and quotient rows. The success fixture uses a synthetic uniform initial-state design, not a demonstrated stationary-data acquisition protocol. The stationary crossing obstruction does preserve a uniform law exactly. Larger n entries are algebraic counts, not executed exponentially large models.

## Persistent hidden-memory extension criterion

A sound stronger extension is available if exact deconvolved parity identities are established under a stationary exploratory behavior law, exploration assigns every deployable action conditional probability at least p_min>0 independently of hidden state given the available history, and deployment uses the same full controlled dynamics with an initial full-state law absolutely continuous with respect to the training law. Exact failure events then have behavior probability zero and remain zero under every finite deployed path law. Fresh final bit noise supplies the resulting controlled quotient law even when the full readout state is not Markov.

A density bound R gives a quantitative finite-horizon path likelihood-ratio bound of at most R*p_min^(-(t+1)) through a step using t+1 actions. This can transfer approximate errors but may be exponentially poor in horizon. Absolute continuity, same dynamics and permitted-action support are real restrictions: this argument does not certify new initial hidden support, changed exterior mechanisms, or previously unavailable interventions. It concerns reachable support of a fixed model, not physical absence of every unobserved influence.


## Final positive-route and execution review

The preferred positive route is now stress/Direct_Score_Discovery.md. Its one-score identity is correct for any Boolean proposal f measurable before fresh final noise: the debiased observable correlation equals the expectation of the corresponding pre-noise sign times f, so its deficit is exactly a latent parity mismatch probability. This does not require a conditional-polynomial model, an observed Markov state, or a Gram matrix. It does require the declared independent process-noise law. Zero deficit is an almost-sure equation under the measured law; stationary or per-time evidence and the support-transfer conditions are needed for all-time deployment conclusions.

Pair-copy discovery is valid at the population level: the true next pair has score one; every distinct raw pair differs on at least two noise-perturbed coordinates and has absolute correlation at most c^2. The final nonlinear gate needs its own gap argument, not this copy gap. The source correctly distinguishes exact population discovery from a finite-data proposer heuristic. The candidate universe for simultaneous concentration covers all adaptively chosen output pairs and Boolean gates on three raw pair parities. Alternatively, fresh validation can condition on the entire frozen proposal and pay only for its selected equations.

I independently inspected and reran check_score_discovery.py. It uses 200,000 proposal records and a separate 200,000 validation records. No true pairing enters query selection. The fresh-validation 95% bound on summed mismatch is 0.031894056096056625, giving stationary unchanged-law ten-step transcript total variation at most 0.3189405609605662. The separate same-data simultaneous bound gives 0.649739259806773. These are two individually valid 95% analyses, not a joint 95% event obtained by choosing the better result after looking. The preferred reported certificate is the prescribed fresh-validation result. It is nonvacuous but loose; it is not a physical safety certificate or a uniform hidden-state guarantee.

The persistent growing-family extension was checked separately. With one fair persistent hidden bit common to all pre-noise residual coordinates, every even output parity cancels it. The quotient is uniform conditional on the exogenous hidden/noise path because each update is a bijection of the preceding quotient followed by an XOR translation. Consequently the stationary current-readout distribution does not depend on persistence, while odd and temporal queries can reveal it. This gives a growing discovered component with unresolved persistent memory, not merely fresh hidden randomness. The same-physics, initial-support and action-support conditions remain essential for deployment transfer.

The exact rational persistent checker was independently inspected and rerun. It verifies the order-two hidden-memory one-step equivalence, the growing even-response equivalence, different odd responses, distinct future means for histories sharing the same current readout, and the parity-noise probabilities. The final support-transfer note now correctly states that a single table supports all-time exact conclusions through stationarity; without stationarity the zero-defect condition is required at each time.

The optional regression checker was independently rerun after the adaptive-query repair. It uses degree twelve uniformly over admitted raw pair queries, not a retrospective degree-six promise only for correct discoveries. It uses polynomial-time binary-linear support membership rather than enumerating every quotient parity, and its empirical learner starts only from the supplied task pair. Its conservative confidence bound remains vacuous at 200,000 records. This limitation does not apply to the separate direct-score holdout certificate.

The main moment checker was extended and rerun after my earlier review: it now also generates exact moments under the fixture's own nonuniform stationary law and passes only Gram and mixed-moment matrices to a separate regression function. It recovers the same four-state core exactly. Stationary total variation from uniform is 0.12958536585365854, minimum mass 0.04180292682926829, and Gram minimum eigenvalue 0.6688468292682926. No state preparation is needed for this population-law check; it remains distinct from finite sampled trajectories.

All five supplied Python checks have been independently rerun successfully in their final substantive forms. No unresolved mathematical blocker was found. The claims should remain scoped to their separate universes: maximal moment completions, the direct-score noise-structured family, compact affine certificate families, and reachable-support transfer. None alone establishes unrestricted physical architecture discovery, arbitrary environmental changes, a small physical remainder interface, or original-contract discharge.

## Final report audit

The final user-facing report was checked against the proofs and executable results. Its scope distinctions are appropriate: no exact-zero inference from finite data, no absence claim for all hidden modes, no unrestricted change of environment, known independent process noise rather than generic sensor noise, full initial-support requirements for transfer, charged physical remainder information, and no original research-contract discharge. The report correctly gives the fresh-validation sample count as 200,000 proposal plus 200,000 validation records and labels the ten-step bound loose. A minor wording clarification was requested so the Hoeffding tolerance t names raw correlation error, with the noise-rescaled mismatch bound stated separately; the mathematical formula was already correct.
