# Predictable source charging for statistical telemetry assurance

29 October 2026. Mathematical candidate; no experimental result. This specifies one way to compose a statistical sensing statement with timing/averaging and physical segment proofs without an invalid post-observation independence assumption.

## 1. Source identity and event order

A source token k=(generation, learned_block, capture_frame) denotes one actual error occurrence. Its binary bad event Z_k=1 may simultaneously affect several sensor channels and several overlapping/duplicated reports. A replacement increments the generation where its source mechanism changes; an old pending packet retains its original generation and capture/window source identities.

The token identity is certified by the retained joint model/interface. Matching values do not establish identity. If unresolved models disagree about sharing, retain those possibilities or use a conservative charging scheme sound for each; do not arbitrarily merge charges to obtain a lower risk bound.

At the first permitted exposure/use of a new token, the protocol must do the following in causal order:

1. From the pre-exposure history, select the token or capture action and its certified upper bad-probability bound pbar_k.
2. Reserve pbar_k from a nonrefundable mission risk account.
3. Only then expose the token's random value, directly or through a report/window that depends on it.

The token may already exist physically, but for the theorem its conditional bad probability given the entire pre-charge history must still be bounded. In particular, no correlated measurement of that token can already have been observed unless a valid conditional posterior bound is used. A convenient stronger implementation charges a fresh block/frame when its first member is captured/exposed; all later reuse of that same token is free of *additional* charge, not free of the original risk.

An averaging window exposes the union of its source tokens. Charge previously uncharged ones before observing that window, under a joint-source conditional bound valid at that point. A deterministic always-active capture protocol can instead charge every relevant block/frame before generation; this may be wasteful but avoids hidden selective-exposure issues. Charge selection cannot depend on the current token's revealed value.

## 2. Assumptions

Fix an offline learned artifact on its simultaneous training-confidence event E, of probability at least 1-delta. Let F_(j-1) include every observation used to choose the jth new token (including all other channels, older packets, controller randomness and queue state). For the adaptively chosen distinct token K_j, require

    P(Z_Kj=1 | F_(j-1), K_j) <= pbar_j,

where selection and pbar_j are F_(j-1)-measurable. Fresh independent block/frame innovations with a correctly learned upper rate are one sufficient source model; the theorem needs the conditional inequality, not independence between all reports.

Let the sum of reserved bounds over all tokens admitted in the mission satisfy

    sum_j pbar_j <= rho

pathwise. The sum includes sources that turn out unused after being exposed or whose downstream evidence later expires. No refunds erase past physical exposure. Decisions after seeing reports may be arbitrary causal functions, provided their physical certificates are sound whenever the charged error tokens are good.

A supplied/verified physical-protocol event G covers clock, calibration translation, queue semantics, command actuation, physical dynamics and initial-state premises. On G and on every charged token being good, complete segment witnesses imply no physical hazard B through the final tail. In particular every physically used error occurrence must be charged; missing or stale packets must either be covered by the protocol witness or trigger a pre-certified reserve/fallback, not be silently omitted.

## 3. Theorem

**Theorem (risk transfer by predictable tokens).** Under the stated source and physical/protocol premises, for the fixed learned artifact on E,

    P_deploy(B) <= rho + P_deploy(G^c),

clipped at one. This is a deployment guarantee at training confidence at least 1-delta. If P(G^c)<=eta uniformly over accepted learned artifacts, an unconditional combined bound is at most delta+rho+eta; the three quantities retain their distinct meanings.

**Proof.** The physical segment induction gives

    B subset G^c union {some charged Z_k=1}.

Because each distinct token is charged once and the selection is predictable,

    P(some charged token bad)
      <= E[sum_j 1{Z_Kj=1}]
      = E[sum_j E(1{Z_Kj=1}|F_(j-1))]
      <= E[sum_j pbar_j] <= rho.

For a random finite number of tokens, insert the predictable continue/stop indicator or extend with zero-cost dummy tokens. Nonnegative monotone convergence covers a countable sequence if the pathwise total budget is bounded. Combining the inclusion gives the result. QED.

The controller may select an unusually favorable-looking report and then act. That does not invalidate this proof **if the source was already charged before its value was exposed**. The theorem does not claim the action's conditional risk, after seeing that report, is pbar_j. It bounds the entire mission's bad-source event instead.

This is a union-bound/compensator argument, not a new probability principle. Its intended discovery content is the justified source-token identity and recursive window/queue interface permitting reuse of charges without erasing dependence.

## 4. Online statistical updates

If the same mission updates probability bounds, use a simultaneous/anytime-valid confidence sequence with total failure probability delta, not repeated optional stopping of a fixed-sample interval. All bounds for token j must be chosen from F_(j-1), before its exposure. Let q_j be its true conditional bad probability and tau=inf{j:q_j>pbar_j}. The simultaneous guarantee gives P(tau<infinity)<=delta; the event tau>j is F_(j-1)-measurable, although the controller need not know the true q_j. Thus E[sum_j 1{tau>j} Z_Kj] <= E[sum_j 1{tau>j} pbar_j] <=rho. Any hazard is then included in physical-premise failure, tau<infinity, or a bad charged token before tau. This yields the unconditional joint mission bound delta+rho+eta. It does NOT condition on a future simultaneous-confidence event and pretend that fresh sources remain independent under that conditioning. A separate offline-training confidence statement is available only under Section 2's offline artifact premises. The runtime still obeys the allocated risk account and valid operating/lease premises.

An old block/frame token remains charged across certificate expiry or source reclassification. If the new candidate set splits a previously merged source identity, the old charge may not cover the newly admitted possibilities: the certificate that justified merging has failed and must be handled as confidence/premise failure, or the original charging scheme must already have been robust to that expansion. Do not retroactively claim to have reserved risk before an already observed source. Physical hardware replacement cannot inherit the old conditional source law merely by retaining the same numerical marginal bound.

## 5. Non-vacuous comparison required

The proposed experiment should include shared tokens consumed by multiple queued/averaged reports, where charging each packet separately is conservative and pretending independent errors is unjustified. It should also include distinct fresh tokens where reuse would be unsound. The actual source-sharing inference must come from permitted records under a separated finite family (or another valid statistical method), with its acquisition cost and confidence charged.

A serious baseline supplied the same true source-token interface should implement the same theorem and obtain the same risk accounting. The research target is discovering and maintaining that interface alongside timing and physical scope, not renaming the union bound.
