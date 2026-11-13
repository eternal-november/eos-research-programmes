# What the anonymous-callback construction changes

## Verdict

The construction gives an explicit acquisition-and-completion result for a **selected anonymous FIFO interface**. It is not a strict generalization of the entire earlier discovery programme, and it is not accurately described as removing packet tags while leaving every earlier capability unchanged.

The closest telemetry example already learned queue sharing, capture rules, averaging windows and shared error sources. Its structured FIFO lemma nevertheless observed packet tags and accurate delivery times; its executed queue trace recorded channel, request time, service start and completion. The new API exposes only callback arrival time, payload and position in the current stream. It supplies neither an origin field nor a persistent anonymous rank. Association is derived from measured timing bounds and controlled releases, or certified only to the extent needed for the role outputs.

## Exact assumptions delta

| Dimension | Earlier result | Selected construction |
|---|---|---|
| Raw observation binding | Tagged requests/packets; named reference channels and aligned calibration windows | Anonymous callbacks; addressed requests remain public actions; no callback channel, request, capture, start or completion fields |
| Physical sensing | Calibrated physical references are available during acquisition; source calibration compares packets with references to the same physical samples | No separate direct sensor for the required role-load vector; calibration exposes the safe callback API |
| Queue semantics | Restricted FIFO service, known clock conventions and safe draining | Independent work-conserving, nonpreemptive FIFO servers; unknown fixed routing and per-address duration; known hard duration and delivery-lag bounds |
| Statistical premises | Separate source-family independence, rate and fixed-window confidence assumptions support learned noise claims | Positive timing/binding result is deterministic under hard bounds; payloads and delivery lags may be arbitrarily dependent |
| Physical bridge | Supplied physical load/calibration envelopes and safe commissioning | Supplied protected same-payload role-load/interlock relation, retention lease, actuation deadline and safe tail |
| Learned output | Queue/capture/source structure and reusable assurance interface | Queue partition and duration enclosures from anonymous timing; dynamic association or role-parity invariance despite unresolved individual binding |
| Persistent uncertainty | One fixed mechanism/source interpretation through uses; aliases already allowed in finite candidate languages | One fixed routing/duration world; the actual production callback bijection is retained among all graph matchings |

**The sensing difference matters.** The predecessor's reference access was to its own physical sample channels, not to this newly defined role-load primitive. There is no automatic theorem transporting that access. Conversely, if the new hardware supplied an equally timely direct measurement of the role-load vector, the controller could bypass callback association. Safe addressed trials with informative physical success feedback could also reveal the hidden priority. The negative result therefore depends on the expressly restricted callback-only calibration API and absence of that feedback. It must not be advertised as surviving every predecessor sensing capability.

The no-loss, one-callback-per-request condition and closed production observation horizon are also substantive. They establish that one actual global bijection exists. Honest arrival timestamps, bounded lag, reliable release semantics, empty-queue initialization or an independently certified drain, fixed routing/durations and safe transport from commissioning to production remain supplied. None is validated by the observed timing tests.

## What the construction actually adds

1. **Anonymous acquisition:** solo timing intervals and pair maximum-arrival tests establish queue sharing without assigning either response to its request. The strict separation checks and complete acquisition cost are explicit.
2. **Derived association coverage:** propagated timing windows contain the actual callbacks. Reliability and the closed horizon imply the actual bijection is a perfect matching of the constructed graph; a joint-record oracle is not assumed.
3. **Mission-relative binding:** one common role vector across all graph matchings certifies the physical command even when individual origins remain unknown. Extra graph matchings can cause conservative refusal, not a certified physical impossibility.
4. **Costed useful completion:** a legal release schedule guarantees acceptance on a stated growing class; acquisition, computation, storage, dispatch, idle time, actuation and final tails must fit the original calendar and budgets.
5. **A matched obstruction:** the callback-only two-queue fixture remains observationally symmetric under calibration. Its deadline forces simultaneous fresh service, yielding the stated risk lower bound. A later deadline repairs that fixture using the same already-supplied retention capability.

These are explicit constructions and scope-specific integration results. Earlier finite-signature safe discovery already provides an exhaustive existence baseline, and the operational compiler already permits persistent sensor-map and alias alternatives. Finite hypothesis enumeration, task-sufficient partial identification, matching algorithms and robust planning are not claimed as first discoveries here.

## Comparison rules

- The **tagged baseline for the new experiment** means the same selected FIFO hardware, payload-to-load bridge, task and budgets, with origin metadata added. It is a controlled comparison, not a claim that the entire older telemetry platform has identical capabilities.
- Serial/drained execution remains legal and can solve the task when deadlines permit. All-address staggering and task-direct aggregate prediction remain legitimate competitors.
- Positive completion needs no payload independence. The independent fair payload law belongs only to the specific negative witness; it makes priority unidentifiable through the permitted callback stream.
- Hard timing bounds are not confidence intervals. No new statistical learning guarantee should be inferred from the deterministic acquisition proof.
- Neither prototype execution nor this comparison validates physical clocks, reliability, safe isolation, source/load coupling or hardware timing.

## Source locations

- *Composable assurance interface results*, §§2–5.
- *Structured discovery lemmas for the telemetry family*, §§A–C and E: calibrated references, observed packet tags, timing conventions and synchronized physical sample windows.
- Accompanying telemetry implementation: `queue_trace`, `physical_probe`, `diagnostic`, `calibration` and `discover`.
- *Discovered assurance frames*, §3, Theorem A: finite separated safe diagnostic signatures and exhaustive interface discovery.
- *Local operational certificates before global state reconstruction*, §1: finite sensor-map and alias alternatives, persistent selectors, and the distinction between record consistency and statistical confidence.
- *Safe acquisition, anonymous joint binding and useful completion*, §§1–8: selected API, physical bridge, construction, obstruction and baselines.

Comparison reviewed 31 October 2026. This is an assumptions comparison, not an additional theorem or a hardware acceptance claim.
