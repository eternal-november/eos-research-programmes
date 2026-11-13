# Structured discovery lemmas for the telemetry family (draft)

Pre-experiment, 29 October 2026. These are candidate sufficient premises for a restricted family, not assertions that the example already meets them. The general design remains in `design/Telemetry_Coupled_Process_Cells.md`.

## A. Safe finite impulse-response identification

Consider a supplied finite-memory load envelope

    x_i(t) = x_i,base + sum_(j,l=0..L) b_ijl u_j(t-l) + w_i(t),

with nonnegative coefficients on a finite grid of spacing Delta, b_ijl<=b_max and known disturbance bound |w_i(t)|<=eta_w. The independently calibrated reference reports x with error at most eta_ref. The baseline x_base is known; if instead estimated from a separate measurement, charge its additional error. This is an FIR synthetic load class, **not a generic RC thermal model**.

In a certified empty-tail state, one diagnostic impulse u_j=epsilon followed by L zero commands produces reference responses epsilon b_ijl with total error eta=eta_w+eta_ref. If epsilon Delta>2 eta, nearest-grid decoding uniquely identifies every b_ijl from the complete measured tail. If the baseline is measured separately with the same error, use total difference error 2 eta and require epsilon Delta>4 eta. All rows are measured and their reference-readout cost is charged.

If x_i,base+epsilon b_max+eta_w<=C_i for every i, and all-off flushing/reset is safe from the actual initial state, each singleton impulse and tail is safe in every candidate world. There is at most one nonzero command contribution at each measured time. Executing n such probes identifies all columns in n(L+1) diagnostic ticks plus resets, with n^2(L+1) scalar reference samples if every output is measured at every tick. This is not a lifetime partial-identification saving.

A sufficient physical recursive observer stores the last L command vectors with their actual values (or a proved smaller equivalent state). After identification only nonzero lags/scopes need affect each output computation. Replacing the controller does not permit erasing pre-replacement command tails.

## B. Exact FIFO partition discovery

Assume a finite collection of telemetry channels assigned to unknown disjoint unit-rate servers. Each server processes at most one packet per tick with a supplied deterministic tie order. Delivery timestamps are accurate at the tick granularity, packet tags are observed, no packet losses occur in this restricted lemma, and diagnostic requests are legal. The queue capacity is at least two, or overflow is explicitly exposed and distinguished. An empty initial queue state is certified; draining time is paid.

Issue one request for channel i and one for j at the same boundary. If they use different servers, both complete at the first service boundary. If they use the same server, they complete at distinct successive boundaries. Thus the experiment identifies whether i and j contend. All n(n-1)/2 pair probes identify the equivalence relation and hence the partition. Processing/report timing itself does not create physical load in this lemma; all cells stay in a separately certified low-load mode while testing. If requests affect actuator timing or heating, that interaction must be included in the safe envelope rather than ignored.

The crude acquisition cost is O(n^2) pair experiments and their resets. This exact procedure is not claimed efficient or new. Bounded server groups yield small discovered protocol interfaces, but do not by themselves make acquisition linear. Stronger batching may be investigated only with its own proof.

Capture-at-request versus capture-at-service is distinguishable for a channel by deliberately placing its request behind another packet, provided capture timestamps with the stated event semantics are part of raw metadata. A singleton server with no legal self-queueing may make these rules observationally identical; it need not be assigned an unjustified unique internal rule. If capture timestamps are absent, distinguishing these rules requires a nonconstant physical/reference trajectory and a separation proof.

## C. Averaging memory: a sufficient identifiable subclass

Suppose a channel reports the uniform average of its last w physical samples at capture, with w in {1,...,W}; physical-sample timing and whether the current sample is included are supplied conventions. Let A_w(z)=(1+z+...+z^(w-1))/w. After physical identification, select an input with nonzero physical response polynomial B(z). The averaged impulse response is B(z) A_w(z). Different widths w produce distinct polynomials: B is nonzero and the polynomial ring over rational coefficients has no zero divisors, so B A_w=B A_v implies A_w=A_v and w=v.

A sequence of safe singleton impulses and captures covering the full L+W response therefore separates widths in the noise-free case. With bounded reference/report errors, require the minimum difference between candidate response traces to exceed twice the total comparison error (including the propagated physical coefficient/reference uncertainty). This finite minimum can be computed before acquisition from the permitted class and selected probe; if zero, the chosen probe is not distinguishing. If no channel input gives a nonconstant physical response, width may be unidentifiable and irrelevant to this restricted input class, but is not thereby known for a later expanded class.

The ability to obtain the required captures is a protocol premise: if a shared unit-rate server cannot capture all channels at all required times, repeat the same certified physical impulse with different scheduled capture positions, or use a proved legal schedule. Every repeat costs time and physical/reference observations. No simultaneous full-rate sampling through a single shared server is assumed.

A recursive averaging observer retains w-1 relevant physical samples or their joint uncertainty relation. Pending packets captured before a replacement retain their captured payload/window and original calibration identity. Queue length plus latest report alone cannot implement this state.

## D. What remains to be proved before this can pass the target gate

The preceding lemmas identify finite physical responses, a FIFO partition and averaging width under deliberately strong transparent conditions. They do not yet establish the intended result:

* A genuinely statistical sensing certificate with dependence and adaptive sampling semantics must be used in a non-vacuous assurance conclusion, rather than decorating a hard bounded-noise example with confidence vocabulary.
* A single jointly realizable mission/replacement witness must use physical, queue and averaging history together and establish strictness under the refinement law.
* The example must prove a small contextual replacement interface. A sparse learned direct graph alone is insufficient under feedback.
* Evidence retraction must distinguish expiry of numerical observations from expiry of the structural stationarity/frame premise. Restoring possible queue-sharing edges can enlarge the entire boundary.
* Cost comparisons must charge the O(n^2) probes/reference observations above if this procedure is used, plus native certificate checking, translation, monitoring, reacquisition and failed/refused replacements.

No experiments have been run for these lemmas, and no overall target acceptance is implied.

## E. Source-block discovery from averaged packets, without a raw-noise oracle

For the canonical width-two fixture, let primitive block/frame errors be iid across distinct frames and independent across distinct blocks, each equal to +e with probability 1-p and -e with probability p. Within a block/frame the same occurrence is shared. This source-family premise is supplied; finite matching observations do not prove it among arbitrary stochastic laws.

A synchronized two-sample packet with a correctly interpreted window has error in {-e,0,+e}, with probabilities

    a_minus=p^2, a_zero=2p(1-p), a_plus=(1-p)^2.

Commissioning reference measurements for the SAME two physical samples yield their average with error at most eta_ref. If e>2 eta_ref (plus any other charged packet/reference error), nearest-category decoding recovers the packet's error category exactly. Thus the acquisition uses ordinary averaged packets and calibrated physical references; it does not assume access to the hidden primitive error bit.

For channels in the same source block, their synchronized packet categories agree surely. For distinct blocks having common p, they disagree with probability

    q(p)=1-[p^4 + (2p(1-p))^2 + (1-p)^4].

For block-specific rates, use q(p_i,p_j)=1-sum_c a_c(p_i)a_c(p_j). A supplied finite rate set avoiding deterministic endpoints gives a strictly positive computable minimum q_min across all distinct-block possibilities. Use N disjoint two-frame windows, so the decoded category tuples are independent across trials under the declared source class. Declare a pair distinct if any mismatch occurs; otherwise tentatively same. With at most P=n(n-1)/2 pairs,

    N >= log(P/delta_block)/q_min

makes the probability of any distinct pair never mismatching at most delta_block, since (1-q_min)^N<=exp(-N q_min). Same-block pairs are never split under the error-bound premises. On this event all pair classifications give the true equivalence relation. If an observed tentative relation is not transitive, retain a conservative candidate family or abstain rather than force an arbitrary partition.

If rates are also to be learned, the finite-grid categorical-law separation theorem in `Discovered_Assurance_Frame_Theorem_DRAFT.md` applies to these decoded triples, with a separate confidence allocation. Alternatively obtain valid binomial/multinomial upper bounds on p from this specified sampling design. Rate estimation cost cannot be omitted or confused with the substantially easier pair-mismatch block test. A preexisting calibrated rate bound is permissible only if openly supplied as a premise, not reported as a learned result.

Calibration windows must be synchronized in physical acquisition-frame identity, not merely delivered next to one another. If capture rules or queue timing are still uncertain, first identify enough protocol semantics to certify synchronization, or preserve every possible window interpretation in the inference. A shared FIFO that services multiple packets within one physical frame can support synchronized frame windows if the supplied sample/clock model makes this true; otherwise repeat legal experiments with their full time and reset cost.

These acquisition windows are intentionally disjoint for the iid inference. Deployment windows may overlap, and their original source-frame incidence must then be retained exactly. An overlapping packet is not a new independent calibration sample.
