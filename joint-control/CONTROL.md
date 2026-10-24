# Coupled control, actual service and one shared resource stock

Status: derived component construction with an exact rational checker and kernel-checked arithmetic certificates. The source is [SOURCE](SOURCE.md), frozen for initial work at 504faf8e8a72570e9fec758d587db60c25651c3a. The information and evolution interfaces below are concrete targets coordinated with their constructions; final C closure requires their checked source realizations and the common-domain integration audit. This file does not report the full research program complete or repository acceptance.

## Prior-result decision

[✓] Sadraddini and Belta, [Distributed Robust Set-Invariance for Interconnected Linear Systems, arXiv:1709.10036v1](https://arxiv.org/html/1709.10036v1), §§II-B–IV, especially Assumption 1, was rechecked on 2026-10-23. It supplies distributed robust-invariance constructions with delayed state/input knowledge. Its reliably available relayed state/input information is not this source's corruptible raw evidence and unknown actual effects. [✓] Usevitch and Panagou, [Adversarial Resilience for Sampled-Data Systems under High-Relative-Degree Safety Constraints, arXiv:2102.05014v1](https://arxiv.org/html/2102.05014v1), §II-A and sampled-state formulation, was rechecked for adversarial actuation, bounded inputs and sampling. Sampled full-state knowledge does not supply the present inquiry service. No new theorem from either paper is imported here without its assumptions.

The selected mathematics is ordinary robust linear feedback, the induced infinity norm, interval workload accounting and induction. These are not novelty claims. The task-specific work is deriving their actual inputs from differing local information, independent faulty effects, contamination/maintenance, timing, service and one joint resource budget. A general barrier-function theorem would not eliminate those adapters. This targeted search was not an exhaustive control-literature or novelty survey.

## C1: robust local feedback under actual-effect interfaces

Consider the two-coordinate source branch. Let d select k>0 and a deterministic finite quantizer Q_u with |Q_u(z)−z|≤q_u on its admitted range. Every intact decision executor issues u_i=Q_u(k hat{x}_i) using its own current decoded vector. The two coordinates are quantized independently. Actual effects can be delayed; a good effect at time t is one for which the actual output obeys

u_i^effect(t)=k(x_t+epsilon_i(t)),  ||epsilon_i(t)||_infinity≤eta.

This is a conclusion to obtain from inquiry, bounded physical change, command quantization and effect realization. It is not a primitive good-estimator or good-actuator assumption. The set of good effects is analyst-only. A policy does not receive that set, the true model, a cure flag, or any other actor's estimate.

At each t let b_t≤F paths have arbitrary effects in [−2,2]^2, including compromised decision executors, independently compromised actuation, unreconstructed code, healthy maintenance holds, and old queued effects. The other g_t=n−b_t paths satisfy the displayed relation. This is one conservative projection of the same joint domain/execution scenario, not independent per-role faults. In particular two separately counted faults on one path do not manufacture two independent adversaries.

Write rho=a_max+c_max and assume 0≤a_min≤a≤a_max, 0≤c≤c_max. Let ||omega_t+varpi_t||_infinity≤Omega. For a prospective operating radius R≤1 require

lambda=k(1−F/n)−rho>0,
B=k eta+2F/n+Omega,
B≤lambda R,
delta(k−a_min)≤1,
k(R+eta)≤2.

Also require the actual-service inequality

(1−F/n)(2−k(R+eta))≥s.

These are explicit sufficient inequalities on primitive/information/evolution outputs; their failure is not an impossibility theorem.

**Guarantee.** If ||x_t||_infinity≤R and the actual-effect interface holds, then ||x_{t+1}||_infinity≤R. Every good prescribed effect is physically admissible, and the actual average throughput in each coordinate is at least s. Different correct recipients may have different decoded vectors and commands. Agreement on a state estimate or a command is unused.

**Proof.** Sum good-path effects as g_t k x_t+k sum_good epsilon_i and retain the actual hostile sum. The matrix multiplying x_t has diagonal 1+delta a−delta k g_t/n and off-diagonal delta c. Its entries are nonnegative under the stated tick bound. Its infinity norm is 1−delta(k g_t/n−a−c). Thus, writing r_t=||x_t||_infinity,

r_{t+1}≤(1−delta lambda)r_t+delta B≤R.

This deliberately overbounds the good-error term by k eta rather than using its smaller g_t/n factor. Nonnegative coefficients justify substituting r_t≤R. Every good effect has magnitude at most k(R+eta). Since actual v_i=2+u_i, a good path delivers at least 2−k(R+eta) in each coordinate; an arbitrary bad path delivers at least zero by its physical alphabet. There are at least n−F good paths. Summing actual contributions proves service. Nothing filters hostile effects or substitutes a command/receipt for a contribution. ∎

The same argument gives a parametric influence/error/time comparison. Increasing F decreases lambda and increases B; growing evidence/effect age increases eta; growing probe/repair disturbance increases Omega; stronger coupling increases rho. A change in these quantities has an explicit consumed margin. Exactness is not asserted for this scalar-gain controller class or for arbitrary source controllers.

## C2: time, initialization and a concrete invariant

Use n=13, k=8/5, delta=1/1000, R=4/5, a,c∈[9/200,11/200], eta=3/50 and Omega=1/50. The full initial query remains ||x_0||_infinity≤1/2. It is not replaced by one known state or by a controller-selected subset.

On the source safe box K=[−1,1]^2, physical actuator limits alone give

||x_{t+1}−x_t||_infinity≤delta D_x,  D_x=11/100+2+1/50=213/100.

For any first exit argument this bound is available on the already safe prefix; it does not assume the desired invariant in advance. Twenty ticks of source information age, total nominal measurement/calibration/row quantization error at most1/500, and at most four further ticks of effect age yield

eta_I≤1/500+20 delta D_x=223/5000,
eta_effect≤eta_I+4 delta D_x+(1/1000)/(8/5)=10749/200000<3/50.

The last term accounts for command quantization error q_u=1/1000. A finer quantizer is permitted. The source gives finite rational packets; exact unbounded real messages are not required. Clipping to the physical alphabet does not alter a correct command because the derived magnitude172/125 is strictly below2.

Intact startup paths hold the supplied baseline u=0,v=2 until the first fresh feedback can have its actual effect. At most24 ticks are required by the information and effect schedule. Even pessimistically allowing every physical input to take any value in [−2,2]^2 during that interval gives

r_t≤1/2+24 delta D_x=6889/12500=0.55112<4/5.

The same finite-prefix induction establishes K membership used in this calculation. Correct startup baseline output has higher throughput than the later lower bound. If some correct feedback arrives earlier it is already covered by the same physical-input safety bound and the established effect-error/service argument; a baseline/feedback mixture causes no missing phase.

For F=4, the exact constants are

lambda=1297/1300,
B=2377/3250,
lambda R−B=217/3250>0,
Y_coordinate≥54/125=0.432>0.3.

Thus the full startup interval preserves K and ends inside the recurrent radius4/5 region; C1 then extends the guarantee. The same policy works uniformly over all stated a,c values, all compatible domain maps satisfying the derived supports, all admitted causal adverse effects, and different correct recipients' estimates. This is an indefinite actual-service result conditional on the constructed source interfaces and persistent supply/timing premises, not a finite simulation guarantee.

**Initial-contamination reserve.** Initial dirty state must not disappear from the support count when the first estimate is published. The evolution proof may directly bound the full early union by four using |P0|≤1, persistent support≤1, one recent acquisition and one healthy maintenance outage. Even if it instead conservatively requires F=5 for489 additional ticks after first feedback, the full query is still supported. Then lambda_5=1137/1300 and B_5=2877/3250. Starting from r0=6889/12500, affine-envelope increments decrease, so

r_t≤r0+t delta(B_5−lambda_5 r0),

and at t=489 this is12159729223/16250000000<4/5. The temporary service floor is48/125=0.384>0.3. Once the actual restoration argument gives F=4, C1 applies forever. This is a finite-phase lemma, not a false claim that radius4/5 is invariant under five persistent bad channels. Larger initial unions require corresponding evidence/support recalculation, not just this physical estimate.

## C3: the source operations supplying the bounds

The primary information realization uses21 actively acquired scalar sources per coordinate (42 rows), tolerating at most q=10 invalid rows per coordinate under every compatible domain map. Correct responders compute their own coordinate medians. Their primitive passive observation is only a function of x1+x2; it does not supply these rows for free. The actual inspection, origin, timestamp/epoch, finite buffer and transport construction must establish that the nominal majority rows meet eta_I. A changed reply path, compromised interpretation or old valid exposed credential is included in q rather than declared truthful.

A concrete joint ownership family has21 reporting footprints, each owning at most one row apparatus of each coordinate and at most one requester endpoint. Thirteen footprints also contain the target decision/actuation role; maintenance paths physically affect only their named targets. Compatible maps may permute these attachments while preserving the per-footprint capacity bounds. Initial nonpersistent exposed/access/contaminated footprints, including local and pending-world queues, have union at most one; initial persistent exposures remain in the separately counted persistent footprint; later target acquisitions number at most eight; the persistent footprint union, including faulty tools and irreparable/nonrewritable powers, has size at most one. Therefore at most ten reporting footprints can be exposed in this positive regime. These are projections and union bounds in one scenario; no independent fault probabilities or extra uncounted initial identities are assumed. Additional pure-sensor/path failures must fit that same union or increase q and the relevant costs. A different ownership map must recompute its actual per-group bad rows.

For restoration take eight bounded-size writable blocks, not eight arbitrarily large machine words. The declared physical write bandwidth must cover the largest block. Halt and boot each cost one operation tick. Fresh inquiry after boot includes12 ticks of drainage/slot clearing followed by publication within8 ticks, so T_I=20. Actual effect/old-queue completion adds L_Q=4. Thus D=8+2+20+4=34; space maintenance starts by S=35, and let each target be visited every P=13S=455 ticks. The full restoration horizon is H=P+D=489. Acquisition spacing at least490 yields at most one event in that horizon; the current transient capability reach OUTSIDE the separately charged persistent footprint, into all necessary query-origin, clock, request/receipt, inference, decision and effect dependencies, has target-union bound one. This is A_dep, projected from named primitive access capabilities under every compatible incidence map; it is not merely direct actuator/write access and is not defined by whether inference happened to be useful. The evolution construction must derive the physical-loss union from these operations, including false writes and off-schedule faulty-tool activity. A permanent tool footprint is never counted as newly clean; copied write/effect authority is not reporting-only leakage.

Under the declared release/opportunity conditions, the resulting union is bounded by persistent support1 + current dependency-access support1 + one uncompleted recent acquisition + one healthy scheduled-maintenance outage, hence four. Initialization retains P0 until its actual reconstruction. The evidence envelope continues counting all ten exposed reporting footprints even after physical repair. Hence restoration does not erase adversary knowledge or magically reauthenticate a source.

These interfaces close a simultaneous induction, not an unsupported assume–guarantee cycle. On the established source prefix, physical caps give state-change and workload bounds. Inquiry then gives useful present-state error from actual rows. The timed write/hold/boot procedure and fresh inquiry establish which effects have resumed; the support-window argument counts the others, including pending old effects. C1 extends the protected state and actual service by one tick. The independent stock argument below supplies every scheduled resource liability throughout the same prefix. No step assumes the final global guarantee as an unexplained input. Final integration must check these constructions and bindings against their actual files.

## C4: genuinely heterogeneous influence

The same result holds for positive weights w_i with sum_i w_i=1, source effects −sum_i w_i u_i and actual delivered service sum_i w_i(2+u_i). The equal-weight mandatory branch is w_i=1/n. The mission K, initial state box, service floor0.3, physical actuator alphabets and actual resource pool are unchanged in this architectural comparison. Module power cost can remain proportional to its own actual work, rather than being identified with its influence weight; the resource proof below uses the conservative unweighted physical maximum.

For the actual joint scenario let beta_t=sum_bad w_i and let beta bound every admitted beta_t, including the weights of halted, contaminated and delayed-effect paths. Replace F/n by beta in C1. Then lambda_w=k(1−beta)−rho, B_w=k eta+2beta+Omega, and the service floor is (1−beta)(2−k(R+eta)). The proof is identical after summing weighted good-error vectors; no identity-dependent gain or hidden true fault set enters the policy. Unknown weight assignments are covered uniformly by taking beta over all source/domain alternatives.

An explicit unequal family has six weights101/1300, six weights99/1300 and one weight100/1300, in any assignment consistent with d. Their sum is one. At most four lost paths have mass at most101/325. The same k,delta,R,eta,Omega give

lambda_w=6453/6500, B_w=2397/3250,
lambda_w R−B_w=921/16250>0,
Y_coordinate≥1344/3125=0.43008>0.3.

The information protocol, restoration schedule and shared resource liability are unchanged. This is a nonempty heterogeneous positive family, not a formula whose only supported instance has equal influence. Its gain, noise/latency and faulty-support margins depend on the actual influence weights. Much greater concentration is a meaningful boundary: one path of weight2/3 and twelve paths of weight1/36 have the same roster but let ONE currently compromised path force net outward control even against maximal opposing action from every other path. That direct access can persist forever under the original current-dependency bound one; the source does not need four conservative impairment-envelope terms to become four permanently malicious actors. The mean-state drift argument in C6 then proves source failure, without calling a failed sufficient inequality impossibility.

## C5: recurring inquiry and repair use one finite stock

The concrete compatible cost convention is an exact-source instance, not empirical measurement of hardware. A different application supplies its primitive costs/capacities and reruns these inequalities. No global resource authorization gate is introduced.

The information construction caps actual per-requester work at intact source ports, uses finite fixed origin buffers and fair quotas, and accounts for pre-admission traffic. Nominal rounds start every10 ticks; a provider's9-tick requester cooldown also bounds repeated Byzantine requests. Its derived all-interval liability is at most25L+500 resource units per recipient over any interval of length L. This includes continuous compute/ingress cost, partial jobs at both ends and source processing induced by hostile requesters. Across13 recipients this is325L+6500. Report-only stolen keys do not automatically acquire requester-origin or write authority; any such additional access must be represented and charged. A quota on intact software never constrains Byzantine hardware.

Separately charge physically compromised apparatus at FULL physical capacity. In the concrete ownership family, each reporting footprint contains at most two row apparatus and one requester endpoint. Each row apparatus can perform at most two sample/position actions per tick (cost at most five each), emit at most1024 bits/tick (cost at most one per64 bits), and perform at most10000 bounded ingress/compute operations/tick (cost at most one): at most27 units/tick. A requester endpoint adds at most16 egress plus2 compute units/tick. Thus the whole footprint costs at most72 units/tick outside actuator and maintenance charges. The construction conservatively allows130 per footprint, preserving spare capacity instead of relying on a Byzantine software quota. One fresh row sample may serve all13 recipients, while all13 distinct replies are actual messages:832 bits fit the declared1024-bit egress. If an implementation instead needs13 independent samples on one apparatus in a tick, its physical cap and costs must be changed before claiming this instance.

At most ten distinct physical inquiry footprints can be compromised in this instance, by the actual initial/acquired/persistent union. That claim is about the physical union, not inferred merely from an abstract bad-row count. The resulting extra liability is at most1300L. Reporting-only leakage cannot itself trigger extra physical samples; copied requester authority or a newly compromised apparatus does join this union. Charging all ten at full power forever covers persistent tactics and conservatively double-counts some costs already charged by the request envelope.

Actual ordinary actuation costs at most sum_i,j v_i,j≤8n=104 units/tick, including hostile commands and holds. One nominal scheduled maintenance path and the one permanently faulty tool port can each perform one operation per tick, at cost at most two per operation; faulty off-schedule operations therefore remain included in4 units/tick. No failed attempt is refunded or omitted. For every interval [s,t), the COMMON demanded cost consequently satisfies

C(s,t)≤(325+1300+104+4)(t−s)+6500=1733(t−s)+6500.

Choose one pool with capacity7500, source initial stock e0∈[6500,7500], and replenishment at least1734 per tick. The source update is e_{t+1}=min(7500,e_t+r_t−c_t). These are one finite reserve and one persistent supply, not separately spendable reserves for sensing, actuation and restoration.

**Interval-stock lemma.** More generally, suppose every interval demand is bounded by aL+b, supply is at least a, initial stock and capacity are both at least b, and each transition uses the stated capped update. Then stock never becomes negative. To prove it, fix t and either use the initial time (if no preceding cap was attained) or the last time the stock equalled capacity. On that suffix, telescoping gives stock at least the starting stock minus b plus (supply−a) times elapsed duration. It is nonnegative. Equivalently, expand the recurrence as the minimum over these suffix expressions; all are nonnegative. This also proves every demanded transition can actually be paid. It is not a convention deleting unaffordable runs. Supply below these sufficient numbers is not automatically impossible; a separate actual-cost witness is required.

The same physical events establish the operation-disturbance bound. Conservatively count at most13×42=546 scheduled sampling actions per tick, at most260 additional rogue actions per tick (larger than the actual four-sample physical footprint cap), two maintenance operations and one acquisition event: fewer than810 events. Let each event have an independently bounded side-effect vector of norm at most1/100000; their signs and targets can be adversarial. Then ||varpi_t||≤0.00810<0.01. Together with ||omega_t||≤0.01 this supplies Omega=0.02. These per-operation effects are bounded impulses in this source specialization. Durable changes to code, access, apparatus or launched actuator effects remain in E/Q and their support accounting; this impulse bound cannot erase them. Thus the plant bound and energy bound refer to the same finite operation stream. If a primitive action can cause a larger or unbounded side effect, this numerical source case does not apply; it cannot be silently absorbed as zero-cost sensing.

Fresh reconstruction does not create free extra inquiry batches. The halt/write/boot interval followed by12 ticks of drainage separates the last nominal pre-halt request from the first fresh request by more than the requester cooldown. Arbitrary off-schedule requests from a contaminated or actively hostile endpoint remain under the actual port/footprint bounds and intact receiver quotas. Suppressed invocation or a compromised local scheduler is included in the physical/evidence domain loss rather than becoming an unnamed benevolent scheduler.

## C6: source-valid failure witnesses and adversarial checks

**Repair is mission-consumed.** Use an architectural variation that removes all restorative effects on poisoned targets: halt/hold, write/boot and any substitute capability that could change their retained output are unavailable. Retain the same fixed mission, ordinary source physical limits and finite acquisition allowance. Merely omitting the selected write tape while another policy could still contain or restore the poisoned targets would not support this all-policy claim. Let eight target acquisitions occur at least490 ticks apart, with at most one current target access at once. Each acquisition leaves executable state that emits u_i=(−2,−2) after active access is released. Retained contamination is the mechanism; no additional active compromise is invented. Give every remaining target the maximal inward command(+2,+2), stronger than any local policy can guarantee. Once eight targets are poisoned, average control in each coordinate is at most−6/13. Choose the admitted a=c=1/20 and zero external/operation disturbance. While x stays in K, its coordinate mean m obeys

m_{t+1}−m_t≥delta(6/13−1/10)=47/130000.

Since m∈[−1,1] on K, it must leave within5532 further ticks. If violation occurs before the eighth event that already refutes the mission. This is an unrestricted influence obstruction in the no-repair source variation, not failure of the proposed gain. With reconstruction, the same acquisition allowance and spacing supply the derived small current loss envelope, so eight historical acquisitions need not accumulate eight permanently poisoned outputs. Old reporting keys nevertheless remain counted in q. This supplies the promised substantive restoration comparison.

**Locally plausible over-intervention can harm.** The physical alphabet permits u=(8/5,8/5). Starting at x=(−1/2,−1/2), a=c=1/20 and zero disturbance, misleading high-state evidence accepted without the robust information mechanism can induce every otherwise intact executor to issue that command. The exact recurrence crosses below−1 at tick299. A signed command, successful actuator receipt and high delivered throughput do not satisfy the joint protected state. The robust proof prevents this source-relevant induced intervention by bounding the relation between the actual state and consumed evidence, not by assuming every issued command safe.

**Shared resources do not compose by separate feasibility.** Use a source-admitted static no-maintenance component schedule, not the full cyclic repair policy. Take x=0, exact observations, u=0, zero environmental/operation disturbance and actual actuation cost52 per tick. Assign the thirteen requester phases0,1,...,9,0,1,2. Requests have an explicit16-bit format, within the same finite request-origin interface; replies remain64 bits. Each of the42 row apparatus takes ONE shared sample at invocation+1 whenever requests are pending. Since the phases cover all ten ticks, that is one sample per apparatus per tick after startup. Reply rows are divided into three lanes of14, delivered at invocation+3,+4,+5. A requester emits42×16=672 bits in its invocation tick and receives at most14×64=896 bits per delivery tick. Each row provider sends at most two replies/128 bits per tick. These respect1024-bit physical caps, the two-sample cap, nine-tick per-origin cooldown and the declared deadlines.

Bill actual transmission energy at1/64 per bit and actual raw sampling energy2 per sample. Do not bill a separate sample for every recipient, and do not turn the five-unit per-job UPPER bound into actual consumption. In a complete10-tick period the real query costs are136.5 for requests,840 for shared samples, and546 for replies, totaling1522.5. Even ignoring all CPU/admission energy, queries plus actuation cost204.25 per tick on average, exceeding comparison supply200. With initial6500 and capacity7500, the executable actual event schedule derives a finite deadline by which combined payment fails; its stock is an UPPER bound because CPU cost was omitted.

Separate feasibility is also checked rather than asserted. A concrete bounded implementation formats and parses each nominal bit in at most eight elementary operations, sorts in at most924 operations per publication, and uses at most500 housekeeping operations per processor per tick for scans of at most42 slots or13 origin timers. There are55 such processors, so30000 aggregate housekeeping operations per tick is a conservative bound. With energy1 per10000 operations this gives at most101.0892 CPU energy per10 ticks, including housekeeping. Individual provider/requester peaks fit their declared CPU limits. Query-only demand therefore has rate at most162.35892<200 and a two-partial-period burst less than6500; the interval-stock lemma proves its separate indefinite feasibility. Actuation alone costs52<200. Their shared actual liability nevertheless exceeds200. This refutes independent allocation of the same pool; it does not claim impossibility for every alternative inquiry/controller policy.

**Information cannot be removed silently.** The separate boundary proof must use the fixed passive-sum source subfamily. Its expanding difference direction and indistinguishable complete local histories supply the all-policy obstruction; C does not infer it from rank failure alone. In the positive construction, charged complementary rows repair that missing distinction. A hypothetical useful-information oracle remains only an explicit comparison interface; I must replace it with the actual acquisition, decoding, workload and freshness mechanism.

The quantitative regime also admits simultaneous useful-evidence corruption, a faulty decision/actuator path, a permanently faulty maintenance footprint, and a healthy target temporarily unavailable during scheduled work. All are charged before computing F, q, costs and side effects. The framework does not require every role to fail simultaneously without bound, nor does one successful trace establish these universal conclusions.

## Verification, refinement and remaining integration

`python -B control_model.py --check` reproduces [control_results.json](control_results.json). The checker exhausts5120 multi-affine vertices for the equal-weight one-step source rectangle, retaining independent correct-estimate errors, hostile effects, a/c uncertainty, disturbances and all bad counts0–4. Every point of the overapproximating rectangle is a convex combination in each variable, so the corner checks support the universal one-step bound; the general derivation above explains why this rectangle covers the source. The checker also verifies the heterogeneous-weight certificate, startup/phase arithmetic, and reproducible no-repair, resource and excessive-intervention witnesses. These executable results are first-pass checking, not independent source adequacy review.

[Control.lean](Control.lean) kernel-checks cleared-denominator arithmetic certificates and elementary stock/envelope order lemmas using `Std`, with no `sorry`, native-decision axiom or real-valued control theorem claimed. The positive-denominator rational identities used by those certificates are computed explicitly by the Python checker. The matrix/norm derivation, source interpretation, causal bounds and final modular assembly remain explicit mathematical and semantic proof obligations; do not describe this file as mechanization of the entire physical controller.

The remaining C integration conditions are concrete: independently check I's row/error, epoch/origin and workload results; check E/R's exact persistent/initial/recent/maintenance union and functional horizon; pin the concrete Γ/primitive cost and side-effect map without introducing uncounted capabilities; and compose their actual source statements with the induction above. In particular exposed requester keys or nonrewritable physical authority must not be mislabeled reporting-only leakage, and a changed apparatus capacity must update both energy and side effects. These residuals do not undo the derived control theorem, but they prevent this component alone from closing BC4 or the full Goal.
