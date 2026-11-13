# Secondary regression: one-frame telemetry–dynamics risk witness

29 October 2026. Analytic fixture before experiments; not the whole benchmark or a novelty claim.

**Canonical target:** `../design/Joint_Prospective_Witness.md` uses width-two windows across independent frames and a stronger two-versus-three-token distinction. This file is retained only as a simpler secondary regression, not a competing implementation specification.

## System and useful work

Five zones form a directed ring, indices modulo 5. Over one service epoch, unknown baseline d_i is constant in [0,1]. The supplied synthetic physical law is

    x_i(t) = d_i + (1/2)u_i(t) + (1/4)u_(i-1)(t-1),

with command u_i in {0,1}, empty initial command tails, and capacity C=3/2. This is a finite-memory load model, not an RC thermal plant. A useful job requires two consecutive service slots with u_i=1, starting at a fixed common start; the next slot is included as the delayed tail. Baseline is unobserved during service except through the specified telemetry; commissioning-reference access is not available as an uncharged service sensor.

Each zone independently admits its two-slot job when its reported baseline estimate passes the rule below. Failure is any zone exceeding capacity, whether or not all five jobs complete. This is not a global all-or-none admission rule.

## Statistical and protocol semantics

A capture frame is a block of 16 ticks. For each frame f, one source bit Z_f is shared by all five zones, with independent fresh frames and P(Z_f=1)=p=1/50. A primitive sample has additive error +1/8 when Z_f=0 and -1/8 when Z_f=1. A packet reports the mean of two consecutive baseline samples preceding/including its capture; both samples in each packet lie inside the same frame in this fixture. Thus its error remains the same frame token, not two independent draws.

All physical commands are zero during measurement acquisition. Hence its noiseless sample is d_i. Define

    d_hat_i = packet_i - 1/8.

On a good token, d_hat_i=d_i; on a bad token, d_hat_i=d_i-1/4. Admit the job exactly when d_hat_i<=3/4.

A deterministic one-packet-per-tick FIFO service can realize the following schedules. Its capture-at-service rule and capture/window metadata have been identified from permitted probes. All completed packets are delivered before service begins at tick 32. Allowed packet age at service is 32 ticks, so all three schedules obey the same permissive age contract:

* Original policy P: five two-sample packets captured at ticks 20,21,22,23,24 (all frame 1).
* Safe changed polling P': captures at ticks 25,26,27,28,29 (all frame 1).
* Mixed-frame replacement Q: zones 0 and 1 captured at ticks 4,5 (frame 0); zones 2,3,4 at ticks 20,21,22 (frame 1).

Packet windows start one tick before capture. Each is wholly inside its stated frame. Request timing can realize these service times with the same unit-rate FIFO. The controller policy is selected before these acquisitions, and all relevant source tokens are charged before their first exposure. No already-observed old token is retroactively charged. The known constant-baseline premise makes the older samples physically comparable; their different statistical source identity remains relevant.

## Physical translation and guaranteed risk

If every token used by a policy is good, any admitted zone has d_i<=3/4. Even if its predecessor also runs, during service

    x_i <= 3/4 + 1/2 + 1/4 = 3/2.

An unadmitted zone has no own command and satisfies x_i<=1+1/4<3/2 even when its predecessor runs. Initial and final-tail slots are also safe. Therefore hazard implies at least one used source token is bad.

P and P' each use exactly one distinct token, so their uniform mission hazard bound is p=.02. Q uses two independent tokens; its union bound is 2p=.04 and its exact bad-token-union probability is

    1-(1-p)^2 = 99/2500 = .0396.

For a mission risk threshold rho=.03, P and the genuinely changed polling policy P' are admissible by the composed statistical/protocol/dynamics proof. Q is not merely a union-bound artifact: the next paragraph supplies a matching physical hazard witness. In learning, replace p by a simultaneously valid upper bound pbar; choose a sampling/separation protocol that yields pbar<.03 before claiming acceptance. Training confidence is separate from rho.

## Exact physical counterexample for Q

Set all d_i=9/10, a permissible fixed baseline. A good-frame report yields d_hat=.9 and rejects its group's jobs. A bad-frame report yields d_hat=.65 and admits its group's jobs. Under P, any bad token admits all zones; at the second slot each x_i=.9+.5+.25=1.65>1.5. A good token admits none. Thus P's actual hazard probability is exactly p.

Under Q, the frame-0 group {0,1} contains an adjacent predecessor/receiver pair, and the frame-1 group {2,3,4} also contains adjacent pairs. Whenever either token is bad, at least one receiver and its predecessor both run, so the receiver exceeds capacity at the second slot. If both are good, none runs and all are safe. Consequently Q's actual hazard probability is exactly .0396>.03. This is a realizable whole-execution witness, not independent maxima over incompatible histories.

Moving only ONE zone to an old frame would not establish this counterexample: its own command alone gives at most 1+.5=1.5, so an isolated bad-token admission need not overheat. Similarly, changing admission to 'run all only if every report passes' would change the event to an intersection and invalidate the claimed union witness. These details are essential.

## Non-vacuous completion instance

At d_i=1/2 for all zones, every report yields d_hat either .5 or .25, so all five jobs are admitted and complete under P and P'. Every service load is at most .5+.5+.25=1.25, with safe full tails. Thus acceptance certifies useful sustained work, not only refusal or idling. The guarantee is uniform across unknown d in [0,1], even though actual success and hazard can depend on d.

## What distinction discovery must earn

A coarse interface retaining only each packet's marginal error distribution and maximum age admits both P and Q and cannot justify the .02 uniform hazard claim. A sound conservative check of all such joint-source possibilities cannot accept the claimed .03 bound for Q. A discovered interface retaining (a) which channels share an error block, (b) capture-frame incidence, (c) two-sample averaging window identity, and (d) the one-slot physical coupling/tail can distinguish P' from Q.

This is a strictness witness for retained joint assurance information, not a claim that no clever controller can succeed using the coarse interface, nor that observing data from P alone identifies the needed structure. Safe diagnostic source/queue/physical identification remains a separate obligation. A supplied truthful stateful source interface can obtain exactly the same result; the intended advance must be its justified discovery and maintenance, measured against that baseline.

The larger family should vary unknown physical/telemetry/error scopes, window widths and online replacements; this five-zone analytic seed alone is not a sufficient research demonstration.
