# Finite pulse fields: delivery, freshness and retirement

Status: derived candidate local supplier with a conditional quantitative point, independently checked after parent-tail, charger-cap, sampler-burst and operation-floor repairs. It realizes neither the complete field hardware nor the recurrent family yet. This is an alternative to indefinitely held endpoint settings in [VECTOR-REFRESH](VECTOR-REFRESH.md); its longer active lifetime must be used in that variant's freshness and retirement bounds. A packet's short flight time is not its field-authority lifetime.

## Finite source and endpoint transitions

For each actual channel (source bank, target physical body, target bank, bit), install Q fixed capsule slots and finite trigger storage. A source sampler retains the actual ternary held setting, a finite edge counter and cyclic slot index, and an actual source-bank launch-permission contact. A sampler opportunity captures the current setting, fixed physical destination and slot. Invalid input, occupied trigger storage or insufficient work has a finite rejection outcome. Neither payload nor slot identity supplies P, truthful input or an honest-donor label.

An endpoint slot follows ready -> active -> withdrawing/disposing -> recharging -> ready. A trigger is accepted only when that slot is physically free and its complete reserve E_p is present. Otherwise it rejects immediately; no queued request waits for later recharge and then silently renews old authority. Acceptance reserves its clock, driver and withdrawal profile. Ready plus pending energy is one store. Ordinary payloads cannot rewrite the counter, reset an occupied pulse or select another physical channel.

Expiry uses the pulse's own funded endpoint clock and consumes it once, independently of the source CPU. The actual source-bank cutoff disables every new sampler/trigger/rearming path; funded parent/packet suffixes survive for their bounded time. U may recharge an idle capsule after cutoff, but recharge is not a trigger. A U-powered sampler outside this cutset would invalidate retirement even if each pulse individually expires.

For active slot set A(t), choose c(t)=0 when it is empty and otherwise the value of its least-numbered active slot. This finite, image-blind selector needs no newest-arrival oracle, global epoch or success certificate. An old slot's expiry recomputes the current active set; it does not schedule an unconditional zero capable of overwriting a newer pulse. The last expiring capsule retains its withdrawal reserve. If a new pulse arrives, its reserve supports the new actuation and the old withdrawal cannot override it.

At conforming endpoints, a possible finite-time raw field law retains y in[-f,f] and, on a held command interval, moves toward f*c at bounded nonzero slew, stopping at that target. With slew at least2*f/tau_s, arbitrary prior polarity reaches the selected sign within tau_s. Empty active set reaches zero within tau_w. This is an explicit finite-withdrawal law, not exponential decay relabelled zero. Its work, regularity and implementation remain primitive-realization inputs; if a different response law is chosen its actual settling/withdrawal certificate must replace this one. Repeated equal-value deliveries must not restart a blind transient indefinitely.

Failures of selector, clock, actuator or funding paths may cause wrong, absent or stuck fields within their actual incident footprint. The positive delivery/expiry law is conditional on the required physical suffix being conforming. A healed source does not restore a persistently failed receiver. A programmable realization of these endpoint functions would need its own code/state renewal; the candidate elementary implementation is finite circuitry/physical timing, with no semantic verification service.

## Cyclic availability and complete slot occupancy

Suppose intact sampler and pulse clocks have independent rates in[1,1.01]. Counting n edges from an arbitrary phase gives the conservative interval[(n-1)/1.01,n]. Choose n_s=2^20 sampler edges and n_p=2^21 eligibility edges. Hence

    S_min=104857500/101,  S_max=1048576,
    D_min=209715100/101,  D_max=2097152.

A nominal trigger must actually deliver/activate within delta; disappearance alone is not delivery. With delta=1, adjacent arrivals are separated by at most S_max+delta=1048577. Their eligibility therefore overlaps by at least103808823/101 quanta. Once every active pulse carries the required sign, selector changes cannot interrupt that sign; actual field still needs its paid settling interval.

Let withdrawal<=1000, disposal/control<=1 and full refill<=100000. Complete slot occupancy from trigger launch is bounded by

    L_slot=delta+D_max+withdrawal+disposal+refill=2198154.

Cyclic Q-slot reuse is certified by Q*S_min>L_slot, with strict inequality covering adverse same-time ordering. Q=3 passes and Q=2 fails. This is constructive: from a ready pool, the next visit to each slot comes after its prior pulse, withdrawal and actual recharge, so induction gives admission without a success acknowledgement. The bound applies to the whole slot lifecycle, not flight alone.

The two-slot failure is an actual local continuation: sample at the fastest constant rate, with actual spacing S=2^20/1.01, and choose the first two pulse clocks' phases for their slowest full lifetime. The attempts at2S and3S find their cyclic slots still occupied and reject. The second pulse plus withdrawal ends before the next accepted launch at4S, leaving a zero-field gap of102659448/101 quanta. This is a failure of that local two-slot mechanism, not yet a whole-source losing theorem.

Initialization cannot create free slots. Either pay separate initial-debt slots plus a ready nominal pool, or inhibit launches, drain every allowed initial trigger/pulse/withdrawal and recharge the actual pool before starting its availability proof. The latter starts from the actual cutoff and uses tau_parent+L_slot, including already latched upstream trigger descendants and the admitted initial residual-state bounds, with chargers continuously connected and funded over their required refill intervals. L_slot alone is not enough if a final old parent can launch a trigger after cutoff. Arbitrary initial active fields remain in the initial effect account meanwhile. Reaching a software reset does not establish this physical entry relation.

## Freshness and exact retirement

A fixed-priority selector may prefer an old wrong pulse over newer correct arrivals. Suppose every source-held setting is permanently correct from t_c, with old CPU-setting suffixes already discharged. Earlier wrong triggers arrive by t_c+delta; their accepted pulses expire by t_c+delta+D_max. A fresh correct trigger arrives within S_max+delta. The overlap inequality keeps a correct pulse available when the last old one expires. Thus actual correct field holds by

    t_c+delta+D_max+tau_s.

At the displayed point with tau_s=1000, this adds2098153 quanta to the completed held-vector scan. The earlier S+2delta held-setting bound cannot replace it. The same argument is uniform over pulse reordering and fixed-priority choices, provided nominal cyclic admission and delivery are established.

If c is the actual no-new-trigger cutoff and tau_parent bounds every already latched source/trigger descendant, then at conforming endpoints no old source field remains after

    c+tau_parent+delta+D_max+tau_w.

Knowledge, payload bits and heat may remain; none can start another pulse through that cut channel. The source graph must include every route to trigger or reset the slots. Failed endpoint residue stays charged to its antecedent footprint, even when its payload names a restored source.

One simple formation design prepares the held vector while the launch route remains physically closed. With a ready pool, engagement gives useful field by p+T_form_max+S_max+delta+tau_s. Local preparation must finish before earliest engagement, and the old bank must persist through this latest field-ready endpoint. If the pool is not ready, add its actual drain/refill interval. Execution-ready overlap for an entire scan remains separate. Preparing data does not entitle an independently powered endpoint to replay it before this physical engagement.

## Conditional paid profile and inventory

A candidate E_p=2^26 profile is sufficient if elementary realization establishes setup/acceptance/withdrawal-control work<=2^16, clock-edge work<=16, and driver power<=8 over the full possible profile. Then

    W_profile=2^16+16*2^21+8*(1+2^21+1000)=50405192<E_p.

Pin the nominal-operation floor to1 work unit for this candidate. The profile leaves total residue16703672 and usable margin16703671 above that floor, within the same capsule. The general interface requires E_floor+W_profile<E_p and actual nominal clock/driver throughput above E_floor; positive stock alone would not establish that service. The local clock/funding implication uses a first-exit argument: before a supposed first crossing of the pinned operation floor, nominal clock progress bounds elapsed active time by D_max; all consumed clock/driver/setup work is then below the reserved envelope. It cannot exhaust the margin before completing the active and withdrawal profile. A self-financing future completion is not assumed. Realization must cover all per-prefix work, including selector changes and rejection/control costs assigned to this capsule. These are declared primitive pricing/timing conditions for a mathematical source, not measured device costs or consequences of the VM's unit I/O instrumentation. They may be replaced by a different itemized profile and larger capsule, with all affected storage, refill, heat and timing certificates recomputed.

For K_out=4*d_out*L, Q=3, trigger reserve E_m and recharge time T_r, the capsule/trigger capacity is Q*K_out*(E_p+E_m). Physical receiving placement uses K_in=4*d_in*L, separately from funding ownership. Install explicit source-end caps of2*E_p/T_r and2*E_m/T_r for the two constituent chargers of each slot. Their sum gives the continuous upstream ceiling2*Q*K_out*(E_p+E_m)/T_r, including reset/dump/recharge abuse. A separate connected/funded nominal law supplies actual constant-cap charging until full, with efficiency>=1/2, and thereby establishes refill<=T_r. An upper refill deadline alone implies no upper power cap:100 units can refill within10 at efficiency1/2 while drawing40 and finishing in5, exceeding the mistakenly inferred20. If a source-end limiter itself fails, its actual larger effects need the corresponding fault projection/hard boundary; the nominal funding conclusion cannot reuse this intact-limiter cap. Accepted-packet rate alone cannot bound that demand. The clock/driver work already paid from E_p is not charged again as a second independent withdrawal.

At d=40,L=8192*192,E_m=4096,T_r=100000, there are251658240 outgoing channels and754974720 slot positions. The conditional capsule capacity is50668588184371200 and charger ceiling126671470460928/125 work/q. Sampler edge work<=16 and hard rate<=1.01 give the all-interval envelope4026531840+(20333985792/5)*duration. The latter value is a demand slope, not an instantaneous power cap. Independent arbitrary clock phases can place one edge per channel in a short interval; the4026531840 burst must enter reserve calculations unless actual prepaid edge stores and capped replenishment supply another proved envelope. Processors, the fast source-held-setting write path, other raw records, routing/control circuitry and all uncaptured physical work remain additional. Background-clock ceilings and state allocations require their actual inventory, not an assumed per-array share of one host allowance.

Unused residue returns to the represented U/heat account after authority is spent; it cannot rearm E/T or restart an expired pulse. Every store has one physical location, all disposal heat stays in the common thermal account, and source-end caps protect intact funding boundaries from failed receivers. A small field amplitude does not bound packet energy or its possible conversion into other physical effects: the enlarged mechanical/energy reach map remains a separate load-bearing supplier.

## Reusable interface and source limits

The [pulse constructor](pulse_model.py) takes clock intervals, edge counts, delivery/settling/withdrawal/disposal/refill bounds, actual pool capacity and complete work prices. Its raw price and native-counter/selector realization must cover the returned pool size and edge counts; a constant-price primitive valid only at Q=3 cannot silently certify arbitrary larger Q. Its [record](pulse_results.json) reproduces the declared point,27 boundary parameter cases and local counterexamples, without checking those physical suppliers. It computes a sufficient cyclic slot count and time/work certificates. The source must realize the finite transitions, physical cutset, bounded native operations, continuous recharge and actual effect boundary. Correct vectors, continuous useful force, affordable repeated service and recurrent restoration remain derived consumers.

Required negative cases are an uncut U-powered sampler; a pool sized by flight rather than active/withdrawal/refill lifetime; an expiry that erases a newer pulse; donor-powered expiry clocks that freeze at donor cutoff; occupied-slot timer reset; double-counted ready/pending stock; returning residue into an old rearm path; and late destination rebinding. These distinguish the supplier from a perfect field server. The full source/program and RP0–RP6 audit remain open.
