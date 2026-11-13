# Final frozen operational-discovery experiment

## Lay abstract

The predictor is learned from action/readout records. It discovers the previous readings and neighboring messages needed by two interacting local predictors, and a shared source needed to forecast their correlated updates. We then freeze that program and test it on fresh records under four feedback controllers.

The final certificate supports both short collections of observations and full-run questions: every bounded question about the joint readings at any three times, and every bounded question about the longest run of any joint reading pattern during the whole eight-step execution. For example, it supports whether both channels ever read one, and whether that condition persists for a specified number of steps. The uniform prediction error bound is .040428, with confidence above 95%. Simpler alternatives that remove memory, neighboring information, or correlated updates fail this same data-based requirement.

The intended one-pass protocol uses 210,000 episodes; this investigation consumed 500,000 episodes including two earlier development protocols. Both are far below the preceding 10.24-million-episode example, although the guarantee is deliberately narrower than its all-controller, full-trajectory guarantee. The final result does not assume that the actual environment has the learned finite-memory structure.

## Frozen final protocol and chronology

1. The first development protocol used 10,000 training episodes plus 80,000 holdout episodes. It tested all three-individual-bit projections.
2. A stronger development protocol used a new 10,000-episode training batch plus 200,000 holdout episodes. It tested all three-joint-time projections.
3. We kept the second protocol's trained candidate unchanged. Before generating another observation, we fixed an additional four-monitor grammar and a fresh 200,000-episode validation batch. This third protocol is the **only primary confidence claim**.

The final holdout seeds are **202610301611, 202610301612, 202610301613, 202610301614**, one for each controller. They are the training seed 202610291611 plus 10,000 plus the controller index. These were fixed in the executable protocol before final data generation. The independently trained candidate remains the one from training seed 202610291611. No final-validation observations were used to change its program, probabilities, initial law, controller family, sample size, radius, or monitor grammar.

Total investigation cost is 90,000+210,000+200,000 = **500,000 unique episodes**, or 4,000,000 transitions. The final intended one-pass workflow uses 10,000 training plus 200,000 validation = **210,000 episodes**, or 1,680,000 transitions. Recomputing the exact same seeded dataset to verify a checker is not charged as new acquired evidence.

Relative to the predecessor's 10,240,000 two-step episodes:

| Accounting | Episode reduction | Transition reduction |
|---|---:|---:|
| Entire present investigation | 20.48 times | 5.12 times |
| Predeclared one-pass workflow | 48.76 times | 12.19 times |

These are different guarantee scopes. They are not an improvement theorem for the original full-trajectory, all-controller target. The new controller-specific acquisition batches also require running all four policies, which need not be safe or feasible on physical hardware.

## Final operational context family

For each of four fixed feedback controllers, the finite context family contains:

* all 84 triples of times from times 0 through 8, each exposing both readout bits at each time: a 64-outcome projection law;
* for each of four joint readout patterns 00, 01, 10, 11, the longest consecutive run of that pattern among the nine readout times: a 10-outcome law with values 0 through 9.

This second item includes all 36 run-threshold events as consequences, as well as every other bounded function of each maximum-run value. In particular it covers the event that pattern 11 ever occurs. It does not certify arbitrary joint functions of multiple monitor outputs unless those functions already factor through one declared context.

The initial warmup reading at time -1 is supplied to the controller and predictor and recorded. It is not among the nine tested readout times. Own remembered-change feedback uses that warmup at its first action. The memory and communication access required by the candidate are explicit.

## Exact independent validation

With N=50,000 heldout episodes per controller and fixed radius r=.0231, the union-bound failure probability is bounded by

    4 * [84*(2^64-2) + 4*(2^10-2)] * exp(-2*N*r^2)
      < .041483095327 < .05.

The checker proves this inequality with rational arithmetic and a Taylor lower bound on the exponential. Each empirical categorical law is compared with an exact integer-dynamic-program prediction of the frozen candidate. The largest fit discrepancy is .017327317314981446. Therefore every declared operational context satisfies

    TV(true law, candidate law) <= .04042731731498145 < .05

simultaneously, with confidence at least .958516904673. All [0,1]-valued functions of each declared context inherit that additive prediction bound. This includes data-dependent downstream choice among those functions and among the four certified controllers, but not arbitrary switching between controllers within an execution.

The full-run monitor predictions are calculated by a separate finite-state recursion tracking the physical predictor state, the current run length, and the maximum run length so far. They are not reconstructed from the three-time marginals.

The confidence event uniformly controls empirical projections; it does not assert the physical law is Markov, has the selected input scopes, or has the selected positive shared-source representation. Repeated episodes under each controller must be independent draws from a common stable law, and deployment must match the validated acquisition conditions. A hazard not soundly related to the monitored observations receives no safety guarantee.

## Failed lower-resource candidate programs

The same final confidence event gives the following lower bounds on discrepancy for three specified ablations:

| Simplification | Data-certified discrepancy lower bound |
|---|---:|
| Average away own lag memory | .12196875 |
| Average away current neighboring message | .16683875 |
| Replace joint updates by independent marginals | .17953250 |

All exceed .05. These are independent-data failures of particular simpler implementations, not universal lower bounds on the minimum possible memory or communication under arbitrary recodings.

## Remaining observational ambiguity

Even this enlarged context family is not full-path reconstruction. There are 4^9 = 262,144 possible sequences of the two readout bits. Recording all context probability coordinates imposes at most

    84*64 + 4*10 = 5,416

linear constraints on a full path law. The constant normalization row is already in their span. Consequently a nonzero signed path measure lies in the kernel of the context map. Its positive and negative parts have equal mass; normalized separately, they give two disjoint-support path laws whose every declared context distribution agrees. Their full-path TV is one. Both can be realized causally by drawing a whole path at initialization and releasing it over time; an environment ignoring the actions gives the same construction for every tested controller.

Thus zero operational error does not imply complete path-law identification. This is why the result carries an explicit context signature instead of claiming that any subsequent control or safety question is automatically supported. Enlarging that signature requires a new certificate.

## Artifacts and scope of contribution

`check_monitor_service_discovery.py` is the frozen final script. It writes the raw training and heldout NPZ records, frozen candidate JSON, all holdout categorical counts, exact projection probabilities, exact monitor predictions, and result JSON. `check_joint_time_service_discovery.py` and `check_sparse_service_discovery.py` retain the development protocols separately.

The confidence mathematics is standard finite-class multinomial concentration. The result is a concrete integration of learned executable scope selection, positive correlated recursive prediction, rich operational query typing, independent exact certification, and data-certified failed alternatives. It is not a new concentration inequality, general physical architecture identification theorem, or empirical robotics deployment result.

## Bounded fair-bit implementation (no new data)

The exact numerical forecaster retains the certified bound .04042731731498145 (outward .040428). To run a stochastic simulator with bounded random-bit consumption, use 20 fresh fair bits per tick to draw an integer U uniformly from 0 through 2^20-1, then set R=floor(200U/2^20). The resulting driver differs from ideal Uniform200 by exactly 33/1638400 in total variation. Passing either driver through the same learned threshold decoder cannot increase that distance. Sequential coupling bounds the two eight-step path laws by 8*(33/1638400)=33/204800=.0001611328125, under the same feedback controller. Every declared context is a deterministic function of that path, so the same bound applies to all monitored laws.

Consequently the bounded generative implementation has certified operational error at most .04058845012748145, outward **.040589<.05**, on the unchanged final confidence event. This is a deterministic implementation-transfer calculation: it uses no new observations, model tuning, or additional statistical test. Its resource budget is 20 fresh fair bits per tick, an eight-bit driver register, and ten possible threshold values delivered to each port (four fixed bits per port), in addition to the already charged local memory and neighboring message. The learned uniform initial law on 16 states uses four fair bits once at initialization. The exact checker verifies driver preimage counts and every learned context's decoded distribution. The numerical predictor and bounded stochastic simulator have deliberately separate error bounds.
