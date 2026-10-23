# Same-mission replacement of a protected physical assumption

Status: derived contextual comparison, six checked arithmetic lemmas and exhaustive source-policy checks. This is an application of the retained peer-enforcement theorem, not a new claim of novelty or a second completion contract. The closest control results and their limits remain in [the enforcement source assessment](../ENFORCEMENT-SOURCES.md); the positive replacement uses the actual source kernel and parameter proof already assessed there. [CORE](CORE.md) supplies the execution and mission transport.

## The comparison that is actually being made

Fix the three-brake quantized plant, its one-tick command queues, present-time LOW/HIGH observations, one static joint fault, physical initialization, current-command duty, speed/heat bounds and actual-output mission. A faulty motor requests any integer torque q in 0,...,6. A normal motor requests four. A baseline-only physical limiter supplies effective torque u=min(q,5). In the replacement context the limiter is absent and u=q. The motor request remains an actual adverse choice in both contexts.

The same physical recurrence is evaluated on the effective torque:

x'=max(0,floor((5x+10u-10E)/10)), h'=floor((5h+xE)/10).

Here E is the sum of three actual binary engagements. An intact effect path follows its old queued command. A faulty planner may choose a different command; a faulty actuator may independently engage or disengage. At most one brake index lies in the union of faulty planners and actuators. Motor/output fault status is a separate coordinate of the same f. These fault budgets are not resampled between observation, command, queue, effect and service checks.

Both contexts have the same derived carrier x<=12 and h<=8, the same safety bounds x<=10 and h<=6, the same initial speeds 0,...,4 (at least one for a normal motor), every initial heat 0,...,6, OFF queues, and the same source-family assumptions. Carrier bounds are not safety clipping. Both retain exactly the same actual faulty motor request alphabet 0,...,6. Only the supplier mapping from request to effective torque changes.

A correct ON command is allowed only when actual invocation speed is at least two. This is a stipulated factive conduct rule: false evidence cannot make an unjustified current intervention compliant. Actual delayed engagement below that threshold is not confused with a new command, and faulty-actuator effects remain included in the world-level heat verdict. Actual heat-violation witnesses require the explicitly wider enforcer-force context in the retained boundary tests. The permission rule does not filter hostile effects.

For J>=2 independent devices with separate heat stores, fix any joint fault family whose brake projection satisfies the preceding bound on every device and whose faulty motor/output set has size p<J at most. The unchanged mission requires every speed/heat bound, every compliant-command duty, and actual aggregate delivery at least J-p at each physical tick. The output of a faulty motor may be withheld. A normal motor delivers its actual x'. Positive service is therefore supplied by at least J-p normal chains, rather than by trusting the hostile device to cooperate.

## Three controllers under the unchanged mission

In the limited context all compliant planners may remain OFF. For x<=10 and u<=5, x'<=10 even when no brake engages. Since E<=3, heat stays at most six. On each normal chain, x>=1 gives x'>=floor((5+40-30)/10)=1 even if every brake engages. Correct OFF commands satisfy the conduct rule. Initialization and induction therefore establish the complete local mission, and projection/summation supplies the fleet mission. Exchange.lean proves the arithmetic bounds on arbitrary natural x,h,u,E satisfying these premises.

Removing the limiter while retaining the OFF policy fails. Choose an admitted faulty motor, intact OFF brake paths, initial x=4 and q=6 at each step. The actual speeds are 4,8,10,11. A normal companion continues delivering positive output; the violation is not manufactured by changing the service requirement or assuming every device is faulty. exchange_model.py replays these same requests and the unchanged physical recurrence, exposing the first world-speed failure.

The replacement is the retained local threshold policy: LOW gives OFF, HIGH gives ON. Each planner uses only its own source frontend and memory. With the selected error-one threshold-three interface, HIGH implies current x>=2 and x>=4 forces HIGH. At least two brake indices have both compliant planning and intact actuation. Their one-tick delayed effects keep speed below the bound under all admitted motor requests up to six; the complete proof is the original delayed-enforcement invariant and its quantized source realization. Its service and heat proof uses actual E<=3 even when an enforcer is faulty. The full finite source graph is independently checked again for this exact requested-input wrapper.

No replacement actuator or planner is permanently correct. Every individual brake appears as faulty in an admitted scenario, including an intact planner with faulty actuation. Multiple simultaneous effects, uncommanded faulty engagement, queued faulty commands, and differing local labels remain in the replacement kernel. A planner cannot veto another motor's physical request. The positive theorem comes from surviving local paths and the physical force/delay margin.

## What is replaced, and what remains assumed

The removed premise is the invariant effective-torque restriction u<=5 supplied by a protected motor limiter. The new context admits effective torque six, including the displayed failing trace against the old program. The replacement suppliers are the already present independent brake paths, local threshold sensing and actual queued interventions. The changed controller uses their joint surviving force; it does not insert another component that approves every physical action.

This is a property-preserving context change with a newly constructed policy, not equality of the two trace sets or an improvement of one policy under identical dynamics. A baseline request six physically realizes five, while the replacement request six realizes six. The correct claim is that both contexts have winning policies for the same decoded mission and initialization, and the second tolerates this additional hostile motor effect. The exact effect difference, mechanism supplier and winning-policy witness are explicit.

The assurance argument terminates at declared physical and fault restrictions: finite motor force, nonnegative bounded brake force, the joint surviving-path bound, one-tick response, present-time source coverage, stipulated conduct and actual-output contracts. Nothing proves safety against unbounded torque, simultaneous failure of every brake, arbitrary observation delay or arbitrary stronger enforcer force. Existing executable obstructions exhibit those failures. Removing the limiter removes a particular trusted component; it does not remove the need for a plant model or sufficient honest physical capability.

The old inventory/gate construction in research/PROGRAM is a different plant with a protected exactly-one-effect interface and service port. It remains a conditional specialization of the common core. It is not relabelled as this rotor plant and its physical guarantees are not transported by analogy. This comparison supplies an actual same-plant exchange witness for the general program, while the common-core maps retain both architectures as distinct members of the theory family.

## Reproduction and assembly

RequestedMotor in exchange_model.py inherits the exact peer-brake kernel with the same configuration in both contexts. Its only effect transformation attaches each raw motor request to the corresponding effective-input outcome. It does not alter compliant membership, reports, queues, fault-generated engagement, current duties, delivery or failure verdicts. All raw requests are represented, including two baseline requests realizing effective input five. The source verifier enumerates all local outcomes and actual service ages.

The baseline arithmetic check exhausts the entire displayed x,h,E,u rectangle; the Lean proof covers the same bounds without enumeration. Full reachable-policy checks certify both positive contexts. The unlimited OFF policy has a reproduced admitted failure. The generic decision-boundary bridge is exercised on both contexts and retains requested/effective input, actual delivered output and event metadata in the resulting trace. Its general run theorem then applies to the instantiated source relation; executable probes do not replace that theorem or constitute a verified Python compiler.

Fleet generalization uses the same exact product factorization already established for the source kernel: each global outcome projects to an admitted local effect under the corresponding projection of one f. The product of local invariants is closed. Summing actual normal-chain outputs gives J-p; summing the separate heat stores gives 6J. An independently shared thermal basin or cross-device mechanical coupling would require its own joint relation and is not covered by this product certificate.

Run exchange_model.py --check and Lean4.33.0 on Exchange.lean. The JSON records source fingerprints, exact local graph counts, the replayed failure and bridge probes. Mathematical support, independently reviewed assembly and repository acceptance are separate judgments.
