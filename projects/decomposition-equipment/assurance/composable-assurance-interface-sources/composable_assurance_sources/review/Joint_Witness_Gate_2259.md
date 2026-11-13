# Independent joint-witness gate — 22:59 UTC

Canonical reviewed construction: `design/Joint_Prospective_Witness.md`, width-two overlapping physical-frame windows. The separate one-frame construction in `theory/Joint_Telemetry_Strictness_Witness_DRAFT.md` is mathematically valid but should be marked secondary/superseded; do not mix its e=1/8, d=.9 and .03 threshold with this construction.

## Verdict

**PASS as a prospective analytic strictness seed for proceeding to a scoped constructive implementation and frozen protocol**, with the concrete clarifications below. This is not acceptance of a completed growing-family result, practical efficiency, general heterogeneous discovery theorem, or hardware safety claim. Standard contract/incremental mechanisms are legitimate ingredients.

## Independently checked calculation

Canonical parameters: five-zone ring, x_i=d_i+.5u_i+.25u_prev(t-1), capacity1.5, two-slot positive work; source magnitude e=1/32, iid primitive-frame bad probability p=.02; width-two averaging.

Good window gives U_i=d_i. One bad primitive lowers U_i by1/32; two bad lower it by1/16. At d=.77, all-good windows reject, whereas any-bad windows yield U_i≤.73875 and admit their zones. Each of the two contiguous frame-window groups contains an adjacent pair. If that group admits, second-slot downstream load is .77+.5+.25=1.52>1.5. Thus hazard is exactly the union of used bad primitive-frame events, not just a loose certificate upper bound.

Aligned windows {-2,-1} have hazard1-.98²=.0396. Splitting groups between {-2,-1} and {-1,0} yields hazard1-.98³=.058808. Budget.05 separates them. Every individual report has the same width-two marginal distribution; all latest-sample ages are≤1. The shared middle source frame must not be double-counted or independently recopied. FIFO microticks can deliver the five packets before the stated decisions under the supplied request-time capture semantics.

At nominal d=.5, even the greatest underestimate accepts all stages, but actual peak physical load is only1.25; all useful jobs and their tails complete safely. The guarantee is uniform risk across admitted unknown d, not guaranteed completion in every d-world. At other d, refusal can be the correct outcome. A controller with a different joint admission rule could change the hazard; this is rejection of the specified replacement policy, not a universal impossibility theorem.

An unadmitted zone has load at most1+.25=1.25, so the no-bad-source physical argument covers zones whose neighbors run as well as admitted zones. Final tails with no own input are also below capacity.

## Statistical theorem check

`Predictable_Source_Charging_Theorem_DRAFT.md` correctly uses pre-exposure, distinct-token accounting and conditional probability bounds. Its union-bound proof does not require report independence. Exact .0396/.058808 calculations additionally use the fixture's independent primitive-frame law. With a learned upper probability pbar, a sufficient accepted bound is2pbar≤.05; an exact known-independent-frame certificate can use1-(1-pbar)^2≤.05. The true p=.02 cannot be used by the online checker unless identification has actually justified that value/bound. Training confidence remains separately charged. Source evidence expiry cannot refund past risk or retroactively authorize a formerly uncharged source.

## Clarifications to close before numerical execution

1. Specify commissioning background as constant during baseline-plus-pulse comparisons, or include its allowed change in identification error. A low upper bound alone does not identify impulse coefficients against drifting background.
2. Subtracting a separately measured baseline adds two reference errors. With error1/128 each, total coefficient-response observation error is1/64 and nearest-grid separation requires greater than1/32. The stated response spacing1/16 still passes; fix the explanatory accounting.
3. State the concrete width/capture candidate set and legal separating queue schedule. Width{1,2} plus a known direct.5 coefficient admits the displayed half-pulse gap1/8 >2(1/32+1/128). Candidate rows without a separating response must remain unresolved or follow a separately verified safe suite. Do not claim full identification uniformly over unidentifiable class members.
4. Operational commitments and charge points must precede first exposure of their frames, including cached reports and queued partial windows. The existing prose declares this correctly; implementation must reflect it.
5. Compile and test the contextual frame, queue migration and complementary proof reuse, including dirty separator-cache invariants. No local-cost or amortization result follows merely from this seed. Strong incremental and coherent baselines get the same discovered evidence/semantics.

## Remaining research milestones

Actual safe acquisition from unknown parameters/partitions/window semantics; a growing interacting workload and maintained validity episodes; accepted/rejected replacements with full initial/pending state; faithful same-information baselines; all discovery, reference, confidence, construction and maintenance costs. Replicating this seed does not by itself establish these results.

No experiment was run in this review. No access/authorization blocker.
