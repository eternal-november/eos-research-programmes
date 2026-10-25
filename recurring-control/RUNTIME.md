# Finite stored-program realization

Status: derived operative component construction, not a global effective-support or full RN/IA theorem. [INFORMATION](INFORMATION.md) supplies its information interface; the renewal/control proofs must establish and consume its source conditions. This is an exact-discrete mathematical machine, not a production firmware or empirical processor claim.

## Actual image and interpreter

The nominal program in [runtime_model.py](runtime_model.py) is1904 bytes of eight-byte instructions in an8192-byte/65536-bit writable image. It uses loads/stores, bit reads, bounded32-bit arithmetic/Boolean operations, comparisons/branches and the source's bounded sensing, transmission and actuator operations. Parsing, two insertion sorts, dead-zone arithmetic and peer-image generation are instruction sequences. No opcode means median, useful estimate, good donor, clean image or successful repair.

| Byte range | Actual state |
|---|---|
|0…1903|Resident instruction image, also read as data by peer copying|
|4096…4099|Mutable identifier/configuration|
|4100…4103|Mutable local phase|
|4104…4107|Drain counter|
|4108…4111|ADC milliunit result|
|4112…4115|ADC completion-valid state|
|4116…4119|Signed mutable calibration CAL, nominal0|
|4352…4623|Thirty-four actual held64-bit input words|
|4864…4999|Thirty-four32-bit sorting slots|
|6144…6271|Thirty-two scratch registers|
|6272…6275|Instruction pointer|
|8191, bit7|Physical route-control bit65535|

Remaining bits are explicit zero-initialized padding and are still overwritten during reconstruction. No second full image is hidden alongside the first. To generate a peer image, the routine reads its own actual resident code bits, generates the target ID and coherent future phase, initializes drain16 and writes zero elsewhere. Donor correctness must follow from the renewal invariant; there is no canonical image server.

Each powered invocation starts at instruction0, whose actual bytes may be corrupt. PC and registers live in the image. Default PC advancement precedes executing the instruction, so a malicious STORE to PC can change later control flow. Unknown words are inert bounded instructions. Timeout stops further execution without undoing accepted prefix actions. Power removal executes no routine and does not clear world actuator latches. A separate stored bad program continues issuing negative flow/deployment and wrong maintenance fields after release, and repeatedly changes its route-control bit.

## Nominal schedule and local information

Use M=65536, S=65600 and P=34S=2230400. The routine reads its own stored ID and phase; it receives no true x, hidden coefficient, fault/cure flag, donor-validity bit or global time. Invalid IDs take a bounded zero-output branch, not a guaranteed safe-world outcome. Phase is normalized modulo P.

Every nominal powered invocation issues g=1. Let target=floor(phase/S) and offset=phase mod S. A role whose ID equals target issues zero maintenance fields. Other roles issue one positive contact field at offsets0…3; one contact plus one addressed image-bit field at offsets4…M+3; two negative contact fields at M+4; and zero fields otherwise. Each emitter has magnitude at most1. The actual guard/zero sequence must establish harmless fields before a nominal target is halted. A poisoned target's held fields remain part of the adverse physical contribution.

The source samples its own row when phase mod10 equals ID mod10. The next phase transmits only if actual ADC_VALID is set, then clears it. One copy goes to each of34 recipients:2176 bits within4096. Sampling and broadcasting are staggered, with at most four nominal sources per tick. ADC completion is a world operation at the next tick; no program flag creates a sample.

The receiver parses each actual physical input word, placing absent/invalid/out-of-range values at sentinel0. Two in-place insertion sorts produce the ninth value of each17-row group. The integer command is

    q(m)=sign(m)·min(1500,floor(8·max(|m|−53,0)/5)),   u=q(m)/1000.

The program implements toward-zero quantization, a.053 evidence threshold and a1.5 issued limit, while faulty physical outputs retain their2-unit source cap. Input words can differ across recipients. Physical port position, not the payload's claimed identity, defines the row.

At boot DRAIN=16. The routine issues u=(0,0) once at that value, then issues no new u for the other fifteen drain ticks. It still samples, transmits, deploys and follows its maintenance schedule. Feedback begins at B+16. The one fallback has arrived by B+4; the first feedback arrives by B+20 and cannot be overwritten by a late fallback. No FIFO assumption is used. Steady every-tick commands can nevertheless have held age8, not4.

The phase increments once at the end of a nominal invocation. All scratch registers are explicitly zeroed, leaving a unique final scratch state and PC at program end. An unpowered role performs none of those instructions. Its phase must be physically reconstructed; it does not catch up by reading analyst time.

## Coherent image generation and bounds

For bit k issued at local phase c, the routine generates boot phase as (c+M+1−k) mod P. Under the aligned schedule c=(c0+4+k) mod P, all copied phase bits represent (c0+M+5) mod P. This is a future residue, not a changing clock snapshot. Nominal arithmetic has no unsigned underflow or overflow: a scheduled bit satisfies c=target·S+4+k, and every relevant intermediate is below2^32.

Opening/closing and donor-support premises are renewal obligations. Conditional on them, the last bit applies at t0+M+4 and actively issued closing fields apply at B=t0+M+5. Active closing establishes the exact first powered invocation; passive release alone cannot. Actual emitter settings return at B+1, engagement by B+5, source reporting by B+13 and quiet-drain feedback by B+20. The common conservative interface is D=M+30; boot alone is not full return.

The selected interpreter charges256 bounded word operations for processor invocation/setup support and32 per decoded elementary instruction, including bounded decode/address overhead and fixed padding. Capture, ADC completion, queue and driver work are separately budgeted below; off-power behavior follows the source contact law, which inhibits writes into local RAM while world queues and held effects continue. This is a finite source-machine realization, not measured Python runtime and not an atomic high-level algorithm oracle. At most6242 instructions fit200000 operations. Hardware limits additionally cap packets, samples and staged settings; accepted prefixes survive timeouts.

For nominal code, non-loop instructions execute at most once on a path. The code contains238 instructions. Broadcasting has at most34 iterations of three instructions; parsing has34 iterations bounded by29 instructions. Each17-element insertion sort has16 outer iterations, at most136 shifts and at most16 terminating comparisons, giving at most1747 instructions per group. Hence

    instructions ≤ 238 + 3·34 + 29·34 + 2·1747 = 4820,
    word work ≤ 256 + 32·4820 = 154496 < 200000.

This conservative bound covers every held-word value, finite ADC state, counter and ID accepted by the nominal instruction image. Invalid IDs skip the long path; phase normalization and a drain decrement add no unbounded loop. Arithmetic and address bounds are explicit. It is an upper demand bound, not a lower resource-failure witness.

The source additionally budgets4096 bounded word operations per body per tick for I/O/driver work, with world queues, held outputs and selector drive advancing while the processor is unpowered. Input capture and ADC writes into local RAM remain disabled by the physical power contact; the allowance does not introduce a bypass writer during reconstruction. A conservative fixed-record implementation bound is34 captures×8 operations +2 ADC completions×16 +at most8 due/held and5 new actuator/selector records×20 +128 in-flight signal slots×20 +64 new signal records×12 +128 bank/control operations =4020≤4096. Records have fixed widths and physical slot counts; malformed words cannot create an unbounded queue traversal. The checked FixedSignalBank realizes the source queue transition with128 actual bounded records, a fixed scan that retains/delivers old contents and rebuilds available indices, and at most64 enqueues. It explicitly preserves delayed old words and rejection when initial capacity is full. This is a realization of the already-declared primitive queue relation with fixed transition logic; it is not an extra protected stored program or a classifier of correct content. Any programmable implementation would have to include its code/state in the source fault/reconstruction scope. Source-world arithmetic used to simulate q or x is not charged as peer CPU computation. Transmission energy, analog sampling and actual force/flow/selector work retain their separate source prices. Any overlapping bookkeeping is a conservative positive overcount, never a lower-cost failure witness. Global extra liability is34·4096·10^-6=.139264 per tick; with the control component's900.8 bound this remains below supply901.

The executable prefixes debit this upper I/O liability, so their recorded stock is explicitly a lower-stock certificate; it is not claimed to be a measurement of actual I/O consumption. Nonnegative lower stock suffices for all actual costs below the admitted allowance. Absolute times in simulator dictionaries represent bounded remaining-delay registers and do not enter any local policy; fixed channel/actuator capacities bound the required physical record inventory.

The block-level reference independently implements parsing, sorting, image cases, scheduling and command arithmetic. Tests compare its actions and every local memory byte against actual VM execution. The general correspondence is justified by block semantics and loop invariants: parsing writes exactly34 slots; insertion moves one larger value and decreases its index; image generation follows the bounded address cases; every used register is initialized; final clearing makes the full post-state agree. Finite tests challenge, rather than replace, those arguments.

## Source binding and checks

Input capture copies actual wire words, possibly false, into fixed per-source registers. It is not a truth oracle. CAL at4116 affects each actual conversion and persists after release. Complete peer writing initializes it to0. A calibration-only source fault leaves an otherwise intact recipient owing the response duty; the test confirms that its median still uses other sources correctly.

The route bit schedules a physical selector change one tick later. Old motion, old packets and retained adversary knowledge remain. A common upstream rewriter of all34 actual words would be a different source branch, not one bad row and not automatically an executor fault. The maintained information proof and its counterexample expose that boundary.

Executable evidence includes:

- full action and byte-for-byte memory comparison against the independent reference;
- all65536 image addresses executed through the actual repair bytecode block;
- an opposed-field complete-image reconstruction projection and a partial copy that leaves actual bad code;
- release with continuing bad code, and a timed-out bad loop retaining its earlier command;
- delayed selector motion, old wire words and retained handles;
- calibration corruption and actual addressed removal;
- denied versus achieved engagement under the same opposition;
- three64-tick full-source commissioning prefixes executing all34 local bytecode machines;
- occupied finite signal-bank startup and restart across all initial source roles and all boot sampling residues, with off-power RAM capture disabled while world queues advance.

The prefixes include actual q/bit writes, power, ADC samples, per-recipient words, selectors, g/u/emitter latches, engagement, flow, shared stock and plant evolution. Two use non-FIFO u arrivals; one also carries two prestart ADC jobs per body due at tick0. New sample requests pay their two-unit liability at issue, while physical sample attempts/results/impulses occur at next-tick completion. Prestart jobs add at most136 unpaid initial liability. The completion count, not request-plus-completion double counting, enters the205 physical impulse envelope. They exhibit different correct commands, persistent post-release behavior and old fields acting during halt. All handles are known to the strong adversary initially; only actual reach changes. Grid residue is explicitly within the source w_env budget.

These prefixes are not a full repair cycle or an infinite rotating-history proof. The65536-bit reconstruction executes the actual nominal maintenance prefix and clock-finishing block, advancing donor phase from stored state. The skipped sensing/sort/control blocks do not write donor code, ID or phase and cannot change those field outputs. Its physical forcing uses a conservative lower bound on contributors and upper bounds on opposing fields, so it is a positive local envelope certificate, not a claim that all34 bodies simultaneously realize every extreme. It is not a disguised full plant simulation. Universal donor availability, no propagation, phase recurrence and mission preservation remain the renewal/control proofs and their checked assembly.

[Information.lean](Information.lean) checks the stated discrete information core, not the whole interpreter. The result record binds this code, its documents, the formal module and shared source. Reproduce with python -B runtime_model.py --check; optimized Python is rejected. No whole-program completion or repository acceptance follows from this component.
