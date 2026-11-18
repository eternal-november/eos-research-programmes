# Finite vector refresh and physical formation

Status: the standalone common-code scanner is lowered to the ordinary finite ISA and independently checked; the target-local physical refinement and integrated controller remain incomplete. This supplies part of [THRESHOLD-RECONSTRUCTION](THRESHOLD-RECONSTRUCTION.md). Target-specific image generation, source-realizing the new I/O lane, physical timing and the common inventory remain unfinished. The result does not inherit prices, timing or field capacity from an analogous old port.

## Finite ordinary loop

Let L be the complete reconstructed image bit count and d_out the actual target degree. Each source bank maintains K_b=2*d_out*L fixed-destination field slots, one for each target side and bit. A finite cursor j<K_b and bounded scratch registers suffice. The image is read from the donor's actual maintained C; an analyst's reference P is not a runtime server. A common-code target uses the actual code cell and finite bit extraction; target static configuration/startup cells use explicitly implemented finite data generation. Volatile donor state is not copied as a coherent startup image.

A nominal service frame performs its bounded sensing/guard/plant/maintenance work and q>=1 vector updates:

```text
entry: initialize cursor and every consumed scratch/control cell; enter the service loop
repeat each service frame:
    perform bounded ordinary sensing/control/maintenance work
    repeat q updates:
        target := cursor div (2*L)
        side := (cursor div L) mod 2
        bit := cursor mod L
        value := target_image_bit(actual_local_C, target, side, bit)
        set_held_field(target, side, bit, 2*value-1)
        cursor := cursor+1
        if cursor == 2*d_out*L: cursor := 0
```

The [scanner model](vector_refresh_model.py) implements the common-code loop with the frozen ordinary LOADC/arithmetic/branch/IO interpreter, using a75-cell,60-register routine and33 working words. `set_field` is the narrow new source-held-setting I/O subtype; its VM instrumentation cost is not a physical work price. It updates one ternary held-setting cell on an actual fixed port. Invalid addresses have a bounded inert/reject outcome. It returns neither target correctness nor guaranteed field application. All addresses, divisions, counters and intermediate bit operations must fit the finite word layout. A correct loop has no nominal self-code write; reads are coherent because actual C remains fixed over its formed interval. A fault during the interval belongs to its adverse projection instead.

After instruction lowering, let I_update=I_image+I_route+I_set and let I_other,I_loop,D_other,D_pace bound the rest of the actual frame. Under nominal funded retirement rate mu_min,

    F <= (I_other+q*I_update+I_loop)/mu_min + D_other + D_pace,
    Nscan = ceil(K_b/q),   Tscan = (Nscan+1)*F.

The extra frame covers beginning inside a partial chunk. At a proved initialized frame boundary Nscan*F suffices. These are bounds on actual nominal powered service, not arbitrary faulty code. The old hard launch rate remains an upper demand constraint, distinct from mu_min. Enlarging the frame changes the age and withdrawal times of every interleaved control routine; those liabilities cannot be assigned only to vector writing.

## Held settings, finite lanes and delayed arrivals

For each fixed physical slot, an image-blind sampler reads its held setting at intervals at most S. At an intact, actually funded lane, each capture delivers that captured value to its fixed endpoint within delta; this is a raw payload transport law independent of whether the bit is useful or correct. Every old record also has residence at most delta, by delivery or an actual harmless/cancel transition. Faulted or unfunded lanes may drop, corrupt or fail and retain those outcomes under their charged projection. A residence-only promise that each record either delivers or disappears would not establish nominal delivery. A failed sender can choose any value but cannot choose a different source/destination by packet data. Mutable firmware implementing this lane would be part of renewed execution; a raw fixed circuit has its actual finite timing/work/fault envelope. Neither is an unpriced reliable network service.

Once a held setting becomes permanently correct at t, old wrong samples are gone by t+delta. A fresh sample after that boundary is taken by t+delta+S and delivered by t+S+2*delta. Add physical field settling tau_f. This conservative no-FIFO bound is valid even if an older wrong sample arrives after an earlier fresh one. It is not a proof that every smaller bound fails. A stale CPU instruction able to alter the held setting after t violates permanent correctness; its pipeline tail must first be drained or included in the next full refresh.

A hard lane launch envelope sigma_lane+rho_lane*T and residence delta bound newly generated pending traffic by ceil(sigma_lane+rho_lane*delta). Additional initial pending obligations require Q_init+ceil(sigma_lane+rho_lane*delta) capacity, unless an actual prehistory envelope already includes them or they are drained before new nominal capture begins. Residence alone does not prevent an initial overlap overload. The direct layout uses the explicit Q_init allowance and its funded initial stock; arbitrary metadata still needs actual residence/retirement semantics. Source-end allocation/caps prevent one failed lane from spending another origin's entire service. Excess rejected requests remain in the work bill. A setting needs no success acknowledgement; nominal progress is derived from the actual lane and funding law.

Destinations are tuples of source bank, target physical body, target bank and bit. Reinterpreting a stale `inactive bank` address after handover would violate this map. Any multiplexed selector offered to reduce the direct array must prove physical destination and tail preservation; an epoch label alone cannot do it.

## Formation must bound both earliest and latest engagement

At new-bank power-on p, the vector feed is physically disconnected. An actual formation coordinate starts from its established lower stop and must traverse D_form before engaging. With nominal maximum speed v_max, its earliest possible engagement is bounded below by T_form_min=D_form/v_max. Reset-to-stop, no bypass and old-enable drainage are actual source obligations. The coordinate does not inspect P, truth or a READY bit.

Let T_data=T_entry+Tscan+S+2*delta, including old CPU/setting-tail clearance and ordinary initialized entry. Require T_data<T_form_min, so every intact new bank's settings are correct before physical engagement. That gives exclusion, not availability. Separately derive T_form_max from actual initiation, positive progress/lower speed or a finite rank certificate; merely bounding maximum speed permits a stalled gate forever. Correct new vector force is then available no later than p+T_form_max+tau_f. The data-ready upper bound is not a valid upper bound on force availability when the feed deliberately engages later.

During engagement settling, old-bank useful force must survive. If inactive/starting sibling residue has magnitude at most epsilon0, the guaranteed host contribution from one established bank of amplitude u is u-epsilon0. The write condition uses u_eff=u-epsilon0 consistently in both mu and T_write. The unattended-cell adverse-only check must also include any sibling residue not already inside its adverse cap. The write condition is therefore

    g*(u-epsilon0) - b*v - eta > Theta,

where v bounds both banks of an adverse host together. Two-bank CPU overlap alone does not establish this vector inequality. Nominal overlapping vectors must encode the same design-time image at the same physical destinations. Live mixed-version changes are outside this source claim unless an actual compatibility protocol is added.

Let r be the actual new formed-vector boundary and e the old useful endpoint. A sufficient local quantitative join is r<=p+T_form_max+tau_f and e>=p+T_form_max+tau_f. To preserve complete future nontransferable scans, require the actual execution-ready bank intervals additionally overlap by Tscan. These execution intervals are distinct from field-effective intervals: CPU readiness licenses a scan, data readiness licenses engagement, and actual field readiness licenses the write margin. The source's physical progress/geometry must establish these endpoints, not a runtime time oracle. CONTINUITY can then derive a bank containing each complete scan job.

A software-enable alternative would need an actual latch held disabled through isolation, drained old enable writes, correct PC entry and a completed initialization before enabling. Setting `ready=0` alone fails when an old funded enable write arrives later. This alternative remains reserve; the present design exposes physical early/late engagement bounds instead.

## One complete vector inventory

The direct layout has K_out=4*d_out*L outgoing and K_in=4*d_in*L incoming field slots per host. The factors distinguish two source banks and two target banks. At L=8192*192 and d=40, K_out=251,658,240. The earlier2*d*L expression would cover only one target bank per neighbor. Incoming endpoints live where the field acts even when the origin funds them; physical location and funding ownership remain distinct maps.

A candidate finite ledger has

    M_vector = s_held*K_out + s_endpoint*K_in
               + s_descriptor*sum_out Q_lane + M_routing + M_timers,
    C_vector = sum_out(C_sampler + Q_lane*E_packet)
               + sum_in C_field + C_feed.

The ordinary processors, code/private state, capture channels and all other control mechanisms are additional. Hard-rate work accounting includes sum_out rho_lane*(E_sample+E_packet), holding power, incoming receive work, actual field generation/opposition, both processors' arbitrary-code upper demand, guarded access, contact work, rejected requests and other loads. Nominal scan cost supplies its deadline; the hard inventory supplies the demand envelope. An instruction or packet price already including a suboperation cannot be charged a second time, and funded suffixes remain real reserved stores until completion.

Initial/refill bursts, standing leakage and all source-side/receiver-side conversion losses enter the one actual stock model. Holding all per-bit fields concurrently cannot reuse one host-wide power allowance independently for every bit. The array is population-independent for fixed L,d but may be extremely costly; no practicality or equal-resource dominance claim follows. Actual heat placement, coupling sums, source caps and reserve through recurring supply deficits must be recomputed before admission.

## Local falsifiers and next implementation

An old latched SET_FIELD completing after reset can overwrite a fresh value; a non-FIFO old packet can arrive last; bank-name rebinding can redirect an old effect; uninitialized new fields can cancel an old bank; and repeated handover can starve every full scan even with continuous power coverage. Each is a concrete missing-law witness, not a generic concern. The formation/tail/interval/destination obligations above are the corresponding control surfaces.

The standalone loop completed a full80-cell self-image scan across both target banks (30,720 slots,1,695,847 retired instructions), and production-range slices exercised the8192-cell/degree40 design. Independent checks also covered q>K and multiple cursor wraps, invalid design parameters, and exact instruction counts. The routine count is7+55*q+3*wraps; initial/steady frame counts are17+55*q+3*wraps and13+55*q+3*wraps. These are bounded execution plus CFG-derived count evidence, not a test of the future integrated controller. The small complete image is a finite algorithm fixture, not a substitute positive architecture; the full-size general claim also relies on the inspected loop/arithmetic invariants.

The captured-destination countercase starts after the I/O offer captures its physical key. A pending CPU instruction still has logical operands until completion, so the physical refinement must preserve fixed routing across that interval or account for a route change. The harness rejects other legacy I/O because it is outside this standalone subroutine; it is not the full source semantics of arbitrary faulty code.

The integrated controller, target-specific startup/configuration routine, field/pipeline/driver source laws and complete numerical inventory remain open. It is a candidate smaller reconstruction supplier for the reusable core, not a replacement for global support, mission or nonblocking proofs. The next meaningful work is to realize the new field I/O and integrate its actual latency with guard/plant scheduling, then check early/late formation and complete H/resource margins. The scanner and its adversarial launch/completion cases already reproduce in the integration checkout and passed a separate read-only review.
