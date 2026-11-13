# Main stronger demonstration: reusable three-time joint predictions

## Abstract

A learned recurrent predictor can now be certified from 210,000 simulated episodes rather than the predecessor's 10.24 million. The learner discovers which past and neighboring readings each local predictor needs and learns the correlation between their updates. Fresh experiments then certify every bounded question about the joint readings at any three times in an eight-step execution, for four specified feedback controllers. The error bound is less than four percentage points. Three simpler predictors that discard memory, communication, or shared dependence fail the same data-based test.

This reduction is obtained by choosing a reusable operational language rather than asking for every complete-trajectory property under every controller. That change is explicit and essential. No assumption that the physical truth has the learned finite-memory structure is required for the certificate; untested higher-order behavior remains unresolved.

## Protocol fixed before this run

This is a separate run from the 90,000-episode, three-individual-bit experiment. It uses a fresh training seed and fresh holdout seeds. After the earlier experiment, we chose the stronger target and fixed this protocol before inspecting its holdout data:

* NumPy seed 202610291611 for training; controller holdout seeds +100 through +103;
* 10,000 training episodes, 50,000 independent holdout episodes per controller;
* horizon eight; two binary readout channels; warm-up reading at time -1 supplied to the controller and candidate;
* all 84 sets of three times chosen from times 0 through 8;
* all 64 possible joint observations at those three times;
* fixed confidence radius 231/10000=.0231;
* acceptance threshold .05.

The heldout record includes the warmup, actions, and all later readouts. The certified projections include the readouts at times 0 through 8, not the warmup or arbitrary action/history scores. The remembered-change controller uses warmup at its first action. This access is charged, not inferred from a future observation.

The proposal algorithm searches all 64 predictive input masks per port and learns the local tables and shared-source mixture from training transitions. BIC and rational rounding are proposal heuristics, not trusted inference premises. It again selects one own lag, one current neighboring signal, and the own action. The candidate is frozen before the validation records are generated.

## Exact result

The largest total-variation discrepancy between an empirical projection law and the learned predictor's integer-DP law is

    .01647171277107715.

For every tested controller and every three-time joint projection, simultaneously,

    TV(true projection, learned projection) <= .03957171277107715 < .05

with confidence at least 1-.04148309532621838. The four controller-specific upper bounds are:

| Controller | Certified TV bound |
|---|---:|
| Request when clear | .039532506604 |
| Request when busy | .039160750000 |
| Crossed observation feedback | .038725020258 |
| Own remembered change | .039571712772 |

The confidence proof uses

    4*84*(2^64-2)*exp(-2*50000*(.0231)^2) < .05.

The exact checker replaces the exponential by a rational Taylor lower bound, verifies all empirical/candidate TV calculations with fractions, and uses integer dynamic programming for candidate probabilities. This is not an asymptotic normal approximation or a Monte Carlo confidence estimate.

Because this is TV of the full 64-outcome projected law, it supports **every** bounded [0,1] score of the six readout bits at the three selected times. It also covers one- and two-time marginal scores by projection. It does not support arbitrary full-run predicates, adaptive switching among controllers, or claims about other untested controllers. A policy selected once at the start from a fixed mixture of the four is covered by convexity.

## Data-certified failed alternatives

Fixed ablated predictors remove own lag memory, remove neighboring readout communication, or replace the learned correlated joint update by independent local updates. Under the same confidence event, their distances from actual heldout projection laws are at least:

| Ablation | Certified TV lower bound |
|---|---:|
| No own lag memory | .12028875 |
| No neighboring message | .16326000 |
| Independent updates | .17695250 |

Thus all three fail the .05 target. These are failures of specified candidate programs, not lower bounds over every possible alternative encoding or memory allocation. In particular, common-source minimality and unique physical architecture are not established.

## Evidence-cost comparison and limits

This protocol uses 210,000 episodes and 1,680,000 transitions. Relative to 10,240,000 two-step episodes in the previous report, the reductions are 48.76 times in episodes and 12.19 times in transitions. Each new experiment is longer, and the policies now require four separate on-policy acquisition batches. The preceding broad guarantee was full-trajectory TV under every adaptive controller, which is stronger; this is a comparison of useful guarantees at different scopes, not a theorem that the old guarantee is 49 times cheaper.

The separate 90,000-episode experiment certifies all three-individual-bit projections with bound .038263. Its smaller budget purchases a weaker query family. The two experiments together used 300,000 episodes during this investigation. Their separate 95%-level guarantees are not advertised as a simultaneous 95% theorem; the main report uses the stronger run's confidence claim. Reusing the exploration result to choose this new protocol does not contaminate its fresh independent holdout.

The generator, program search, physical limitations, source resource accounting, and acquisition assumptions are described in `Sparse_Service_Discovery.md`. Both experiments use the same interacting recurrent service family, not a new physical benchmark. The operational guarantee requires repeatable IID episodes for each tested policy, a stable acquisition/deployment relation, and soundly observed scores. It does not establish that a physical hazard is represented by those scores, that testing is safe, or that unseen coupling is absent.

## Why this is not full-trajectory recovery

Let four binary observations have either the uniform even-parity law or the uniform odd-parity law. Every proper subset of those four observations has the same law under both alternatives, but the full laws have disjoint support and TV one. Embed those four bits at four different times, hold the other readout channel constant, and add identical independent observations elsewhere. Every three-time joint readout law agrees; a four-time parity question disagrees completely. This is a causal process: draw the parity-constrained vector at initialization and release its coordinates over time. Therefore even zero error for our full query family would not imply full-trajectory TV or arbitrary composition closure.

That boundary is a specification choice, not a defect hidden by the certificate. Enlarging the context family requires an enlarged test and evidence budget. A controller or safety claim outside that scope must not inherit this guarantee automatically.
