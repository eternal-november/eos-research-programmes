# Joint prospective witness: coupled process, FIFO telemetry, averaging and source-frame risk

29 October 2026. Exact mathematical construction for review; no outcome experiment. This specializes the broader candidate. It supersedes any suggestion that the earlier accumulating-disturbance regression is itself a member of this FIR subclass.

## One cluster and physical execution

Five zones form a cycle, with indices modulo 5. During a finite service epoch the background states d_i are unknown constants in [0,1]. This sample-and-hold background regime is a supplied physical premise, not inferred from a few constant samples. Physical load is

    x_i(t) = d_i + (1/2) u_i(t) + (1/4) u_(i-1)(t-1).

Capacity is 3/2. A work stage requires u_i=1 in two consecutive physical slots. All five zones are offered useful stages, which a policy may individually accept or refuse after reports. Deadline and useful-work accounting count partial completions and refusals; no universal completion in every background world is claimed. Delayed tails after the second work slot remain checked. At maximal simultaneous work, x_i=d_i+3/4; a proved upper bound d_i<=3/4 suffices. On the nominal realizable world d_i=1/2, all offered stages complete and peak load is 5/4.

The initial operator class has unknown input scopes and lag assignment, coefficient grid multiples of 1/4 up to1/2, lag ceiling1 and at most two nonzero terms per output. The actual cycle is not supplied. Commissioning modes have a separately justified background envelope d_i<=1/4, constant over each baseline, probe and relevant averaging/tail observation. This different mode must be explicitly exposed and charged; arbitrary service backgrounds need not admit the same probes. Physical identity/reference and the coefficient class are supplied semantics.

## Reports and clocks

Each physical slot contains at least ten ordered telemetry microticks. Physical state/background is sampled at the slot's initial capture event; packets are then served by bounded unit-rate FIFO servers in microticks. Five requests on one server fit within a slot. Actual server partition, capture rule and width are unknown within the declared finite class. For this concrete subclass the candidate width set is {1,2}. True width is2 and true capture is request-time, with each report averaging the samples at its window endpoint and previous physical slot. True queue capacity is at least5; queue overflow has explicit reject semantics.

All sensing windows below precede work, so u=0 and the physical samples equal d_i. A report's latest sample is either slot -1 or slot0, and the service decision is at the end of slot0. Both satisfy the same permitted maximum elapsed latest-sample age of two physical slots (the sample at the start of slot -1 is almost two slots old at the end of slot0). Packets are tagged with channel and sequence; trusted event semantics and clock conversion are supplied. Actual window interpretation is learned/retained rather than inferred from units alone.

## Statistical source and certificate

All five channels in the true cluster share one source block, but that sharing is learned with stated confidence. Primitive source errors ξ_f are iid across physical acquisition frames f, equal to +e with probability.98 and -e with probability.02, with e=1/32. Within a frame every channel sharing this block receives the same ξ_f. A width-two report at endpoint r is

    z_i(r) = d_i + (ξ_(r-1)+ξ_r)/2.

Thus the full marginal report law depends on two independent draws. Use upper estimate U_i=z_i-e. On the event that both primitive draws are positive, U_i=d_i exactly. With either negative draw it can underestimate. The local action rule runs the two-slot stage only if U_i<=3/4; other zones may independently run their accepted stages. Even if a neighboring stage runs, this rule guarantees x_i<=3/2 outside the dangerous-source event for i; if a neighbor does not run, load is only smaller. Include the tail explicitly.

The set of eligible five channels and source windows is fixed/committed before observing any of these source values. Charge all distinct primitive source-frame tokens in these windows before first exposure, including partial queued exposures. There is no claim that .02 is the posterior error probability after an attractive report. Shared tokens are charged once, and already-exposed tokens retain their histories rather than being declared independent again.

## Accepted and rejected changed policies

Original aligned policy: all five reports use window{-2,-1}, delivered or cached before the slot0 decision. An accepted changed policy changes the request microtick order, queue residence and controller scheduling but preserves these five window endpoints and the boundary deadlines; its request traces differ genuinely, while the joint payload/source-window relation and physical service envelope are unchanged. Check the current queue/cached-packet state when applying it; no reset is free.

Misaligned replacement: three contiguous channels use {-2,-1}, the other two contiguous channels use {-1,0}. Each report has exactly the same width-two marginal error law as before, and all satisfy elapsed age<=2 slots. The source-window union changes from two primitive frames to three. Its declared exact dangerous-event probability changes from

    1-.98^2 = .0396

to

    1-.98^3 = .058808.

An operational allocation .05 therefore certifies the aligned policy but cannot certify the misaligned replacement under the same predictable-source certificate. This is not a marginal/age failure: their marginal law and maximum allowed age are unchanged.

For this particular per-cell policy the risk distinction is also realized by a compatible physical world: take every d_i=77/100. If both errors in a channel's window are positive, U_i=.77>.75 and its stage is refused. If either is negative, U_i is at most .77-1/32=.73875<.75 and its stage runs. Each contiguous group has at least two zones. Whenever that group's window is bad, an adjacent pair runs; at the second work slot the downstream member reaches .77+.5+.25=1.52>1.5. If both windows are good, no stage runs and no violation occurs. Therefore any bad primitive among the three used frames causes a physical violation, and no all-good realization does: exact risk is .058808 for the misaligned policy. With the original aligned window the same reasoning gives exact risk .0396. This is a strict risk-budget rejection for this specified replacement policy, not infeasibility for every possible controller. A stronger controller can alter its decisions, and the coherent baseline must be allowed to do so.

For the nominal d_i=1/2 world both replacements' actual stages can remain physically safe; the point is certification against unresolved service-state worlds and the declared risk budget, not manufactured empirical crashes. All rejected replacements and missed jobs remain outcomes, not silently discarded.

## Safe separation margins in the same class

Independent reference error is bounded by1/128. A quarter-amplitude isolated pulse produces a coefficient-grid response spacing1/16, strictly greater than four times reference error1/32, covering the two-reference baseline subtraction before grid discrimination. Under commissioning d<=1/4 and coarse maximum two coefficients1/2, even broad half-amplitude excitation has load at most1/4+1/2=3/4<3/2. Complete pulse tails and queue drains are charged.

For a width1 versus width2 reference trajectory, a safe half-amplitude command on a directly influencing input can produce a rise1/4. The instantaneous versus two-sample average gap is1/8. Combined report-error/reference uncertainty is at most e+1/128=5/128, and twice this is5/64<1/8. This gives a strict distinguishability margin for these two widths once the relevant physical response has been safely identified. If an actual candidate response does not produce this rise, the probe is not silently assumed to work: retain the candidate or use the separately required safe separating suite. The initial class includes rows for which this particular diagnostic is uninformative, so global finite identification still needs the safe-identifiability premise.

FIFO partition acquisition uses paid empty-queue pair tests; signed residual/source-block acquisition uses paid synchronized reference frames and the simultaneous finite-sample confidence construction described in the main design. Calibrating all samples simultaneously may require repeated safe trials for unknown shared-server capture rules. Source-block identification error, operational.05 allowance and physical premise failure remain different quantities.

## Growing family and honest reuse claim

Replicate K five-zone clusters, with actual clusters/permutations unknown. The supplied candidate universe allows bounded scopes/server groups/source blocks; it must not name the true clusters. Introduce repeated two-slot stages, ordered jobs, and windows/deadlines across service epochs, with stage alternatives only where physical meaning supports them. The exact seed above is a regression for each cluster; richer workloads must still be constructed and checked, not presumed to follow from replication.

A changed controller checked to preserve the full joint boundary relation can reuse complement proofs. Whole-system coherent rechecking should match capability. Generic incremental verification given the same discovered semantic frame can match the local check cost. The prospective benefit is learning the usable frame and amortizing its construction, not claiming new dependency invalidation. Cross-cluster physical paths, shared source blocks or pending queues widen the frame and may erase locality.

For expiry, the sample-and-hold/background/source stationarity lease must cover the entire report window, decision, work and physical tail. Otherwise reject before commitment or reserve a hard-envelope fallback. Restore expired support alternatives and propagate semantic frame changes, while retaining past risk charges and past-valid claims. This is not yet an implemented online maintenance protocol.

## Calibration through averaged packets, not an invented raw-noise sensor

The independent reference measures physical samples, not primitive telemetry error draws. For the true width-two transducer, subtracting the reference average from each packet yields one of {-e,0,+e} up to reference error1/128. Adjacent residual values are separated by e=1/32>2/128, so their categories are distinguishable. Collect synchronized **disjoint** width-two windows to obtain independent residual-category trials. Channels sharing a primitive source block and the same window have equal categories; independent blocks differ with probability

    q = 1 - [(1-p)^4 + (2p(1-p))^2 + p^4] > 0.

The finite p-grid gives a positive lower bound q_min. The pairwise no-mismatch test therefore uses the same (1-q_min)^N bound without pretending to observe individual primitive signs. p can be bounded from the finite residual-category law using fixed-sample simultaneous confidence; alternatively the mean residual identifies 1-2p after amplitude is known. Overlapping windows are NOT iid samples for that calibration calculation. Discovery uses disjoint windows; service retains the actual overlapping source-frame structure.

When candidate averaging/capture mechanisms remain unresolved, reference/data likelihood or separation must quantify over each candidate. Do not first assign the desired window interpretation and then use its conditional statistical test as though that interpretation were certain.

## Review corrections and learned rate interval

Independent review passed this as an analytic seed for a scoped implementation/protocol, not as a completed benchmark. The actual learner uses a simultaneous valid interval [p_lower,p_upper], not the simulator's true .02. A sufficient aligned-policy certificate is p_upper<=.025, yielding the conservative two-token union bound<=.05 (or use exact independent-frame bound 1-(1-p_upper)^2). To prove the misaligned policy exceeds .05 uniformly over the retained interval, require 1-(1-p_lower)^3>.05. If the interval is wider, retain uncertainty and report an inconclusive/refused certificate rather than inserting true p. Finite-sample rate learning can be expensive and is charged explicitly.

For request-versus-service capture separation, use a known competing FIFO request to delay the tagged probe request by a physical sampling boundary while the safely excited physical reference changes. Queue size, empty initial state, deterministic order, microtick/physical-boundary conversion, and the entire physical tail must be checked. A same-slot delay during sample-held physical state is not a separating experiment. The generic candidate lemma must furnish this legal schedule or leave the capture rule unresolved.
