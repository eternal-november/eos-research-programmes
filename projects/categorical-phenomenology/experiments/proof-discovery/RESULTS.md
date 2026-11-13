# Actual results

Exploratory final version v3. All operation costs include discovery, unsuccessful search, and certificate verification. The common eight-case subset was classified after the first run; the original workload did not change.

| Method | Original transfer /12 | Compositional /8 | Controls /8 | Proxy total | Acquisition |
|---|---:|---:|---:|---:|---:|
| Definitions only | 0 | 0 | 8 | 3,871 | 108 |
| Training theorem only | 1 | 0 | 8 | 744,632 | 740,526 |
| Ordinary early stop | 7 | 3 | 8 | 749,756 | 740,526 |
| Guided early stop | 7 | 3 | 8 | 770,369 | 761,139 |
| Ordinary full completion | 12 | 8 | 8 | 763,527 | 758,014 |
| Guided full completion | 12 | 8 | 8 | 782,685 | 777,399 |
| Cold rediscovery | 12 | 8 | 8 | 9,695,041 | 740,526 |
| Supplied normalizer* | 12 | 8 | 8 | 6,643 | 1,634 |

*The supplied normalizer has human-selected lemmas. Their proofs are charged, but human discovery/selection is not. It is not a competing unsupplied-lemma learner.

All rows completed under the 10m cap. Under 1m, all except cold rediscovery completed. Under 100k, all discovery methods exhausted their cap before test evaluation; definitions-only proved 8 controls, and the non-competing supplied normalizer proved every test.

## Timing (five independent executions)

| Method | Median CPU seconds | CPU range | Median wall seconds |
|---|---:|---:|---:|
| Ordinary early stop | 0.288443 | 0.271469–0.308051 | 0.288644 |
| Guided early stop | 0.302931 | 0.288370–0.305120 | 0.303133 |
| Ordinary full completion | 0.310218 | 0.273822–0.361466 | 0.310439 |
| Guided full completion | 0.314570 | 0.284057–0.316822 | 0.314886 |

These measurements are descriptive, not a statistically established speed ranking. Guided full completion costs 19,158 more proxy operations than ordinary full completion (+2.51%) for the same eight compositional successes. Guided early stop costs 20,613 more units than ordinary early stop (+2.75%) for the same three successes. Ordinary full completion solves eight rather than three for fewer units than guided early stop.

CPU-cap sensitivity: at 0.05 and 0.25 CPU seconds, all four automatic variants exhaust the cap before held-out evaluation in all three repetitions. At 0.5 seconds all finish: early-stop variants score 3/8 and full-completion variants 8/8. Raw cap overruns are recorded in timing_capped.json; the largest observed was under 4 ms.

## Fixed random-order controls

| Seed | Compositional /8 | Original transfer /12 | Proxy total |
|---|---:|---:|---:|
| 11 | 8 | 12 | 764,845 |
| 23 | 8 | 12 | 730,395 |
| 47 | 8 | 12 | 744,583 |

All three preselected seeds solved all eight composite cases. These three seeds are not enough to characterize random-order performance, but they rule out presenting the tested guided ranking as the only effective mechanism.

## Verified reuse

The guided early-stop variant directly uses the generated intermediate reversal lemma in proofs of rev_nested and rev_both. Its third compositional success, rev_nested_other, uses generated append identities/associativity plus the trained involution theorem. All three successful statements exceed the proposal grammar bound; none equals a retained theorem. The complete dependency audit is results/proof_and_reuse_audit.json.

The audit replayed 43 saved bundles (39 nonempty), including cold per-target bundles. Across these files there are 207 lemma-certificate entries and 322 test-certificate entries; many repeat across budgets/methods and are not independent examples. Sixteen kernel tests passed. A separate reviewer additionally rejected eight adversarial certificates and tested 500 statement mutations, finding no accepted false statement in an independent small-list check. This does not prove the Python implementation sound.

## Interpretation

Pass: unsupplied intermediate law discovery, formal-in-this-calculus validation, and actual reuse on larger equations.

Fail: a demonstrated benefit specific to failure-guided discovery over ordinary completion. The mechanism is conventional proof-library learning within a fixed language. The results do not support mathematical novelty or a distinctive categorical/phenomenological explanation.

## Accounting audit qualification

The 24 deterministic method/cap combinations were replayed with a separate wrapper recording atomic verification overflow. None performed uncharged kernel work. Timings include search/acquisition and all acceptance checks, but exclude the final redundant bundle replay. CPU caps are soft, with actual overrun reported. Cold rediscovery pays for the same initial training episode before discarding its library; it is an amortization ablation, not the cheapest standalone cold-start solver.
