# Conditional numerical regime for local two-bank renewal

Status: exact candidate arithmetic, with source suppliers open. H and W below are design budgets to be justified by the actual mechanism, not an assumed or achieved repair service. This contribution preserves the nonempty intersection of several timing, force, incidence and plant inequalities, and exposes what would invalidate their assembly. It makes no source-admission, full-program, acceptance or novelty claim. [feasibility_model.py](feasibility_model.py) reproduces all numerical claims using rational arithmetic; [feasibility_results.json](feasibility_results.json) binds the inputs.

The comparison consumes the repaired common-selection scope in [OPERATIONS](OPERATIONS.md), the applied-response overlap law in [CONTINUITY](CONTINUITY.md), and the current two-coordinate candidate in [INSTANCE](INSTANCE.md)/[PROBES P7](PROBES.md). Those coordinator-owned source files were inspected without editing them. They are separate maintained definitions; the numbers here do not replace them. The interpretation deliberately omits a complete runtime, source transition system and actual recovery trace. It retains their missing obligations below. No large pulser coherence window is used.

## 1. Fixed locality and common fault projection

Use R>=6 regions with72 hosts each, N=72R, ordered cyclically. Host h has maintenance edges to h±1,...,h±20 modulo N. Its degree40 is independent of R, the ±1 edges connect the family, and edges cross each region boundary. Each target side has80 private producer bays indexed by (neighbor host, execution bank). The two banks of one neighbor therefore do not share a candidate write lead. A host contains finite inventory for both target sides; the count does not grow with execution time. This topology is a maintenance relation, not a complete communication graph or proof that observations arrive.

Use one effective-domain cover from the same history for maintenance, information and regional outputs. A global cover of at most6 hosts implies at most6 in every40-helper neighborhood and at most6 in every72-host region, because both are intersections with that global set. Thus the regional unusable fraction is at most1/12. This is a strong sufficient global regime; it is not inferred from independently chosen regional budgets. The checker tests1656 translated placements on rings with6,7 and10 regions.

The distinction matters: bad hosts69,...,75 give regional counts3 and4, but the clean host76 has all seven in its helper neighborhood. Separate regional bounds of6 therefore do not imply the local bound of6. A source allowing independent regional arrivals needs a spatial envelope for overlapping neighborhoods, not a silent reuse of this global calculation. Shared dependencies or one propagating writer can reach several effective hosts; host identifiers do not prove a footprint bound.

## 2. Force, ports and a seven-host failure

Take usable nominal maintenance force at least2 per relevant host port, physical cap2.2 per execution-bank/port, disturbance at most1, stiction threshold28 and speed cap1 stroke unit per hardware quantum. A damaged host can use both banks, so its per-stroke adverse cap is4.4. With six impaired helper hosts,34 usable hosts supply at least68 while opposition plus disturbance is at most27.4. Consequently

\[
27.4<28,\qquad68-27.4-28=12.6>0.
\]

Under the declared dead-zone/saturation law this gives retention against unattended adverse motion and unit capped forward progress once the necessary fields are actually applied. Before that time, readiness and stage-alignment conditions remain essential. A startup bank with a stale opposing output can cancel its correct sibling; CONTINUITY records that counterexample. Initial driver isolation or a proved zero/compatible-output prefix must prevent planned startup from creating uncharged adverse force.

At seven bad helper hosts, opposition can be31.8. An enabled unattended stroke with no nominal effort then has dead-zone output3.8 and moves by1 under the speed cap. This is an actual failure of the first-motion/retention mechanism, not merely a failed sufficient inequality. It does not establish impossibility for other thresholds or mechanisms, and a physically locked stroke is not substituted for an enabled one in the counterexample.

There are B+4=84 force ports per neighbor task in this accounting:80 insertion arms and reset/cut/freeze/activation arms. The cap is an aggregate across all cartridge processors on a bank, not a separate new allowance for each powered cartridge. Maintaining all40 neighbor tasks gives a per-bank simultaneous cap of2.2·40·84=7392, and a two-bank host cap of14784. Nominal allocation at2 gives13440. These large values are finite and explicit. They cannot be spent again independently by another task or silently identified with energy. Bypass, blending and additional physical ports must be included in the final aggregate or supplied a separately justified allocation.

## 3. Finite local work, geometry and candidate budgets

The image length L counts inspected storage cells in the actual finite alphabet; L must be at least the complete admitted policy/configuration image size. The examples8192 and65536 do not assert that an8192-byte compiled implementation already exists. Word width, encoding, reference storage, addressing and code immutability are source/runtime obligations.

Provisionally budget at most2 hardware quanta for one bounded per-target micro-visit. A40-entry round robin and one quantum of invocation slack then give J=81 between visits to the same target. This visit handles bounded local work such as one cell/query and cursor advance, not a whole L-cell copy or BL-cell scan. All plant-control, parser, voting, output-update and local bookkeeping work sharing the processor must be included before that two-quantum claim is usable. A bounded raw instruction/rate premise can eventually justify it; an unspecified successful callback service cannot.

Set command residence D=3, reset stroke R0=2D+J+2=89, insertion maximum5, old-contact cut6 and freeze5. These are the retained exact-discrete kernel parameters, not yet a proved continuous/noisy fixture. The scan and stable applied-response bounds are

\[
T_{scan}=(80L+2)81,\qquad T_{work}=T_{scan}+81+2(3)+1.
\]

Twork covers the complete nontransferable scan and its applied response, including old-command reordering and one switching unit. It does not include the later overlap or the whole renewal cycle. Let Bready be a separate conditional parameter for verified reset, initialization of every relevant per-target scan/vote/cache/output field, any clock bootstrap, and the needed fresh-evidence/drain prefix. Use Bready=16384 in the examples, not as a proved startup time. The budget A=1000 for new live information below must fit inside the appropriate prefix. If the actual W layout or startup work requires more, increase Bready and regenerate the dependent inequalities.

The coordinator's [BOOTSTRAP](BOOTSTRAP.md) stored-instruction loop was independently inspected and its record reproduced. It correctly isolates ordinary initialization from full controller readiness and executes3Q+4 instructions for Q private words. Its actual budget must satisfy (3Q+4)delta_exec+B_evidence+B_entry<=Bready. Q is not the image length L. For the separate illustrative Q=8192 case,24580 instructions at one quantum each already exceed16384. At an independently established half-quantum instruction bound, adding evidence1000 and entry3000 gives16290, leaving94. This is a conditional prefix-budget example, not evidence that the full visit can execute within V=2 or that the controller has that working-memory layout. The intended stored instructions, reset entry, private-writer exclusion and unchanged incoming/external state remain the bootstrap boundary.

Let ceil_M round upward to a multiple of10^6. Choose additional power-contact distance

\[
G=\operatorname{ceil}_M(6T_{work}/5+B_{ready}).
\]

At maximum speed1, ready overlap is at least G-Bready, which exceeds Twork. Booting does not certify readiness: this implication still needs the actual image/reset/startup theorem and continued old-side execution. The new effecting driver must remain isolated until its output state is safe. The later physical authority switch retains its own factual and tail obligations.

Set AP=Tscan+2 and A0=AP+3. Substituting B=80, J=81, D=3 and Tboot=Bready into OPERATIONS' displayed conservative budget gives

\[
K=13209L+17426.
\]

The two-bank source must change the kernel's early cut so it cuts the side being prepared while the useful side stays on. Extending activation by G accounts for keeping old power through the new ready interval. The original single-host proof does not itself establish that wiring correspondence.

A trial rearm allocation sums A0+G+R0+6+5+5 reverse-stroke lengths, plus six(J+2D) transition allowances, then rounds upward to a million. Call it Qrearm. This is an explicit length/work allocation, conditional on a permissible ordered path whose each stroke achieves unit progress. That path remains missing; reversing contacts in the wrong order can reconnect stale power/writers or interrupt the useful side. Let

\[
W_* = K+G+Q_{rearm}+1000,\qquad C=\operatorname{ceil}_M(6W_*/5),\qquad H_*=2C.
\]

The last1000 is an explicitly unproved final information/old-effect tail budget. Additional stage-recognition, post-freeze acquisition, load-transfer or clock/bootstrap delays must be charged, not absorbed by a success label. The record reports remaining timing slack for such adapters while retaining C and H*. It is spare capacity, not a proof that those mechanisms fit it.

| Quantity in hardware quanta, except stroke distance | L=8192 | L=65536 |
|---|---:|---:|
| Complete scan | 53,084,322 | 424,673,442 |
| Applied local work Twork | 53,084,410 | 424,673,530 |
| Additional overlap distance G | 64,000,000 | 510,000,000 |
| Ready-overlap lower bound G−16384 | 63,983,616 | 509,983,616 |
| Conditional kernel budget K | 108,225,554 | 865,682,450 |
| Reserved rearm Qrearm | 118,000,000 | 935,000,000 |
| Candidate attempt W* | 290,226,554 | 2,310,683,450 |
| Local period C | 349,000,000 | 2,773,000,000 |
| Candidate return H* | 698,000,000 | 5,546,000,000 |

For independent nominal clock rates in[1,1.01], the exact checks give C/1.01>W* and C+J+W*<H*. Thus a feasible attempt can fit before the earliest next periodic opportunity, and a wait of at most C+J plus that attempt fits H*. This statement is conditional on the actual permissible-entry/rearm mechanism. A calendar does not make a prohibited cut eligible. No actor reads analyst time, a good-set map or a successful-return flag.

There is no circular overlap definition: Twork depends on the scan and applied response, not G, Qrearm, W* or H*. Substituting the whole renewal W* for Twork would require G>=Bready+W*, although W* already exceeds G by positive preparation/rearm costs. The checker records that strict contradiction in both examples. Conversely long physical progress can persist across banks only after the compatible-held-output/stiction argument is supplied; a hidden nontransferable routine of longer duration changes Twork and the geometry.

## 4. Burst, concurrence and retained damage under one envelope

The proposed raw envelope has at most c=2 simultaneously acquired host-domains, acquisition arrivals at most floor(3+lambda u) in every interval of length u, lambda=3/(10C), one persistent host-domain and zero surviving initial debt. Use continuing footprint kappa=1 only as a required no-unassisted-spread result for the effective-support projection. It is not a claim that a producer physically reaches only its own host: it reaches many private candidate bays. The proof must explain why those writes cannot create additional corrupted running/inference/authority suppliers without a charged source event.

If actual useful return removes all relevant retained contamination/authority/effects within H* after final release, INFORMATION's interval argument would give, for a transaction of duration W*,

\[
B_{eff}\le1+\{2+\lfloor3+\lambda(H_*+W_*)\rfloor\}=6,
\]

because lambda(H*+W*)<0.85<1 in both examples. The ratios are lambda C=0.3 and lambda H*=0.6. These expose burst/concurrent load as well as mean incidence; they do not prove strict useful service. To close the source, prove from an initialized prefix with support<=6 that the actual operation returns released roles within H*, and that old powers cannot induce uncharged spread. The numerical inequality cannot establish its own premise.

An explicit raw schedule uses three acquisition streams at k(10C), k(10C)+1 and k(10C)+3. The first acquisition is released at k(10C)+2; the second at(k+1)(10C); the third at(k+1)(10C)+1. Release is processed before a same-time new acquisition. Thus direct control never exceeds2. Each stream's spacing10C implies at most1+u/(10C) arrivals in an interval, so their sum obeys the stated burst3 envelope at every interval, not merely checked endpoints.

At the second burst's offset3, two prior-burst domains have just been released at offsets0 and1; the first new domain was released at2; and two new domains remain under direct control. Retain the actual code damage of those three released domains: five domains can still affect the operation despite only two being directly controlled. With a distinct persistent host, the cover has size6. The executable records those identities and verifies820 finite interval cuts. It performs no successful recovery transition; the global H* clearance implication is still a source obligation. A physical trace must also show that the selected sides are mission-consumed and that the first three-step burst precedes actual effective return. The raw envelope reserves no bank from subsequent acquisition.

## 5. Plant time, complementary information and capacity

The current INSTANCE has two coordinates per region, with two spatial diffusive terms and one nonnegative cross-coordinate term. Its conservative coordinate variation bound inside the box is1.658 per plant-time unit; either sum/difference row varies at most3.316. Use raw row error epsilon0=.005, complete sample-to-effect age budget A=1000 hardware quanta, and tau=1/250000 plant-time units per quantum. Then

\[
\epsilon_0+3.316\tau A=2283/125000=.018264<.02,
\]

leaving217/125000=.001736 reserve. The earlier trial tau=1/200000 fails this row bound. Row inversion ((s+d)/2,(s−d)/2) gives each coordinate error at most half the sum of the two row-error magnitudes; both rows are required. A=1000 must be derived from actual sampling, cache/vote expiry, processing, command and effect delay, not from the slow image-scan budget. Images can be scanned slowly under actual immutability while the live plant feedback remains fast, but the processor/resource allocation must realize both.

With six unusable hosts out of72, the checked P7 numerical consequences per coordinate are upper-boundary minimum flow141/200, lower-boundary maximum flow79/200, and interior actual flow at least23/120. The upper/lower inward collar margins, allowing all three outward diffusive contributions within a .01 collar, are691/15000 and2191/15000. Independent asynchronous bank blending preserves the relevant coordinate interval when both sides actually satisfy it. It does not preserve arbitrary coupled resource constraints automatically. A common joint fault/output/resource history and an admissible two-coordinate input vector are still needed.

The source-probe and written P7 proof were independently checked in the coordinator's working files, including36 row-inversion endpoint cases,64 mixture cases and12 load-transfer cases. The collar proof is valid for absolutely continuous trajectories satisfying the derivative and current-error/output premises almost everywhere. The load relation (1−s)F+eta<=.4 for s>=.9,F<=2,eta<=.2 is correct but conditional on the actual coupler and absence/accounting of additional load paths. Neither relation supplies current factual evidence or a safe physical transfer. This review does not promote P7 to full source closure.

All time quantities need tau. The two example local periods become1396 and11092 plant-time units; H* becomes2792 and22184. These are large, fixed design bounds, not measured seconds or claimed practical performance. A speed cap1 per quantum becomes1/tau stroke units per plant-time unit. Stroke lengths, motor rates, sensor error and processor rates require physical unit/calibration choices; changing the interpretation cannot improve a deadline for free. Arrival rates in physical units are lambda/tau, leaving products lambda H and lambda W unchanged.

The force sum14784 is not energy. A source conversion must charge force/holding duration, both powered banks, CPU work, every offered/rejected raw packet, sensing, movement, bypass and both plant coordinates in one account. As an illustrative accounting compatibility check only, if all-in demand is at most20000 energy units per quantum, raw supply(0,0,60000) repeated and a60000 clip-before-charge reserve survive indefinitely with recurring real drawdown and recharge. At unit force-to-energy cost14784 leaves5216 for every other item; no claim is made that the actual program fits that remainder. The supporting interval-accounting law remains in PROBES. This example supplies neither an energy calibration nor raw delivery/service infrastructure.

## 6. Exact remaining suppliers and reproducibility

The missing construction is specific: an actual two-bank wiring map preserving useful execution while OPERATIONS cuts the prepared side; finite reset/startup and immutable-C semantics with neutral drivers until initialized; current factual permission and bounded entry into an admissible load/isolation region; a bounded permissible rearm order; recognizable closure/compatible stage actions under noisy delayed observation; common least-bay read availability and post-freeze acquisition; complete old-authority/effect removal; the no-spread/footprint proof; actual instruction/cell/query/path capacities establishing V,J,D,Bready and A; shared energy/force allocation and supply interruptions; and the joint initial-family/plant invariant. If any extra stage takes time, charge it in W* and recheck C,H*, the envelope and units. The artifact reports unused strict timing slack but does not fill it with an assumed successful adapter.

Run unoptimized Python3.12 `python feasibility_model.py --check`; `--write` regenerates only the owned JSON after review. The checks cover both image scales, exact timing/force/envelope inequalities,820 raw-schedule interval cuts,1656 spatial placements, the seven-helper failure, row/plant compatibility, and a conditional recurrent-deficit accounting trace. These are exact algebraic and bounded-interface checks, not execution of the full recovery/controller. No additional Lean file is introduced merely to repeat elementary rational arithmetic. Source admission and the full Goal remain open.
