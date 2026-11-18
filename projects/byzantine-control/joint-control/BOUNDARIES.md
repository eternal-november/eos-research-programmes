# Source-level information, influence and resource boundaries

Status: written derivations and independent algebra/source review, with the review's coupling clarification incorporated below. These answer named negative questions in [SOURCE](SOURCE.md); they do not replace its required positive construction. The proofs use ordinary indistinguishability, linear dynamics and cumulative accounting. No novelty is claimed. Reconstruction impossibility, control impossibility and failure of a chosen sufficient certificate remain separate.

## B1 Passive evidence cannot preserve this mission

Consider the fixed passive-sum ablation from SOURCE. No raw heterogeneous measurement becomes available without acquisition; the compared policy has no such acquisition interface. All local plant observations are functions of x₁+x₂, and every other observed datum, initial local memory, scheduling/availability relation and source effect queue can be chosen identically in the paired executions. The same actuator command and queue outcome produces the same additive input in both worlds. Ordinary repair may change stored program state but reveals no extra plant coordinate in this ablation. No faults are necessary for the obstruction: the no-fault, zero-disturbance scenario is admitted. The controller is any deterministic family based on permitted histories, with arbitrary memory and communication.

The particular source slice uses state-independent bounded command/hold queues, fixed equal initial baseline queues, and operation side-effect relations admitting zero for every issued operation. It also admits zero environmental disturbance, and action-based costs/metadata that can match in the paired worlds. The positive construction's independent effect bounds and signed side-effect intervals admit this same slice; its fault-tolerance guarantee must include it. A general state-dependent realization relation need not have this coupling, so passive sums alone would not justify the following argument for an arbitrary plant. This is an explicit applicability restriction, not an added controller observation or an assumed equality of unknown world states.

Let a>c≥0, δ>0, 0<r≤1/2, and start the two source worlds at x⁺₀=(r,−r) and x⁻₀=(−r,r), both in the fixed X_init. Put ε=δ(a−c)>0 and λ=1+ε. Then for every t up to a first failure,

\[
x_t^+ - x_t^- = 2r\lambda^t(1,-1).
\]

**Proof.** At t=0 the passive observations and supplied local memory agree. Suppose the complete local histories agree through t. The same local policies issue the same messages, commands, maintenance and internal updates. Choose identical admissible transport/scheduling/physical delay outcomes and identical additive disturbances in both executions; the selected source permits this coupling. Their additive inputs therefore cancel when subtracting the dynamics. The vector (1,−1) is an eigenvector of the source drift matrix with eigenvalue a−c, so the displayed recurrence follows. Its coordinate sum is zero; hence the next passive plant observations agree. The other observations and local states agree by the coupled source choices. This simultaneously proves the next history equality and state-difference formula, completing induction. If a resource, service or conduct failure occurs first, that execution already loses the full mission and need not be continued as a safe witness.

Two points of K=[−1,1]² cannot differ by more than 2 in either coordinate. Whenever rλ^t>1, both paired executions therefore cannot be safe. Such a finite t exists: induction gives (1+ε)^t≥1+tε, and any integer t>(1/r−1)/ε suffices. Choosing, for example, the allowed a=0.055,c=0.045 proves failure of a policy required uniformly over Θ(d). No selection of the true hidden initial world is allowed. The adversary needed only identical ordinary source choices, not unavailable future information or an impossible coordinated disturbance.

The quantification is over the whole passive-history policy class, not the candidate affine feedback and not a bounded memory search. The result is mission-level safety impossibility for that specified ablation. It is not a theorem that all rank-one distributed observations fail, that exact state reconstruction is always necessary, or that all coupled plants need communication. Giving some actors direct access to the missing direction changes this source interface and must be evaluated as such.

## B2 A delayed distinction has a deadline

In the same source slice, suppose all permitted acquired observations are indistinguishable across the paired executions until tick T, with no other action yielding earlier distinguishing information. This includes an admitted delay pattern that postpones every informative response until T. The preceding induction applies through those ticks. If r(1+δ(a−c))^T>1 and both worlds must remain safe through T before the information can change their physical effects, no local policy meets the mission. With additional actuation delay L and a source coupling preserving identical applied inputs until T+L, replace T by T+L.

The causal order matters: observations available before an action at tick T can alter x_{T+1}; they cannot repair an already unsafe x_T. This is a valid losing latency regime under the same mission and initial query. It is distinct from a sufficient estimator-age inequality: failure of that sufficient inequality alone has no impossibility consequence. The positive construction must provide its own finite operational acquisition and response margins.

## B3 Insufficient independent influence

Use the concrete branch with n equal-effect channels and instantaneous realization as a special case of the allowed delayed relation. Let b channels have persistent independent hostile effect authority, unaffected by software reconstruction. They choose u_i=(−2,−2), corresponding to zero useful delivery. The remaining channels, including any legitimate counterintervention, satisfy the physical cap u_i∈[−2,2]². Choose zero operation disturbance and environmental disturbance, an admitted source slice. Set x₀=(r,r) for 0<r≤1/2 and let m_t=min(x₁,t,x₂,t). Nonnegative a,c imply

\[
m_{t+1}\ge (1+\delta(a+c))m_t+\delta(4b/n-2).
\]

This follows coordinatewise from a x_j+c x_other≥(a+c)m_t and −n⁻¹\sum_i u_{i,j}≥2b/n−2(n−b)/n. If 4b/n−2≥0 and a+c>0, induction gives m_t≥r(1+δ(a+c))^t, so some finite state exits K. More generally a positive outward lower bound on the reachable interval gives its corresponding finite escape estimate. A software command, administrative exclusion, correct state estimate or perfect value agreement cannot enlarge the physical cap in this argument.

This is an unavoidable influence obstruction for the specified direct-authority regime, not merely a failing feedback law. It leaves a real gap between broad sufficient positive bounds and this necessary capacity bound; no exact threshold over the whole family is asserted. A physical mechanism that actually removes the hostile authority or changes B_i creates a new capability context. Its costs and surviving service require their own argument.

## B4 Shared resource exhaustion under continuing service

Let the source stock satisfy e_{t+1}≤e_t+r_t−c_t, e_t≥0, with initial e₀≤E₀. Assume primitive replenishment r_t≤r_max. If each unit of the actual unnormalized delivered flow costs at least η>0 and the mission demands average normalized delivery s_j in each coordinate, then over N complete service windows of W ticks,

\[
\sum_{t=0}^{NW-1}c_t\ge\eta nNW\sum_j s_j + C_{\rm inquiry}(NW)+C_{\rm repair}(NW),
\]

where the latter terms are additional actual nonnegative costs, counted without duplication. Summing the stock inequality yields

\[
\eta nNW\sum_j s_j+C_{\rm inquiry}(NW)+C_{\rm repair}(NW)\le E_0+NW r_{\max}.
\]

If r_max<ηn\sum_j s_j, the mission fails for any N with NW(ηn\sum_j s_j−r_max)>E₀, independent of strategy or attacker quiescence. When the mechanism imposes a recurring minimum inquiry/repair cost, include that actual cumulative term to obtain its sharper endurance or supply bound. Costs required only by a chosen mechanism give a mechanism-specific boundary; they are not automatically lower bounds on every possible controller.

This is an actual-service accounting theorem, not an assertion that lack of a particular resource certificate makes control impossible. It also diagnoses invalid module composition: two modules drawing from one stock must satisfy the single summed inequality, not each separately compare its own cost with the full replenishment. The positive construction must prove a compatible upper-cost/stock invariant under persistent admitted tactics.

## B5 Replacement changes the impairment window as well as precision

Consider an information component whose stated age and postboot completion bounds increase from20 to23 ticks, retaining k=8/5,δ=1/1000,R=.8 and the other source margins. This may be realized by a longer postboot drain while retaining the nominal steady pipeline; using23 as the common age bound is then conservative. Recompute, rather than silently inherit, both numerical interfaces. The effect-equivalent error becomes12027/200000=.060135. At four impaired paths the radius margin remains108149/1625000>0, so an error-only replacement test would pass.

The actual restoration duration is now D=8+2+23+4=37, padded spacing S=38, period494 and H=531. The original acquisition spacing490 permits two new acquisitions in an H-window. The conservative effective-loss bound becomes1+1+2+1=5, and the same radius certificate has margin−301851/1625000. This is failure of that sufficient assembled certificate, not source impossibility: a tighter support argument or another controller might succeed. Restoring acquisition spacing to at least532 returns the four-loss certificate; the27-tick initial interval still fits the source initial box and radius margin.

The old certificate remains a true statement about its old timing/support context. It does not establish its own applicability after the change. This supplies a concrete stale-assurance witness and the X3 replacement consumer: preserve or rederive J_t, time and resource liabilities, not just estimator precision. No Byzantine actor needs to forge a mathematical theorem for stale applicability to be dangerous. Retained ENACTMENT separately supplies positive handling of actually consumed false/scoped runtime certificates under its stated static context; this arithmetic witness is a validity/transition argument, not a replacement for that P evidence.

## B6 Isolation can destroy necessary information while leaving force

Use a source variation in which an isolatable actuator assembly shares its physical feed with the sole acquisition apparatus for all heterogeneous raw rows. Its ordinary command fault can choose its bounded actuator output but cannot sever that feed; the defender's physically stronger isolation operation cuts the feed and the actuator. The operation is not a safe action by definition. Before isolation the observation/effect architecture has the raw-row and surviving-influence interfaces; after isolation the actuator contributes v=0 and every informative raw-acquisition port returns only unavailability. Remaining actuators retain their independent influence, but their only state observation is the passive sum.

Pin the negative slice carefully: the raw apparatus is no longer capable of observing either coordinate after the cut; no separately observed sensor state, side-channel, resource telemetry or alternate reattachment action supplies the missing direction. Initial local memories contain no historical distinguishing sample. The probe/queue/resource outcomes can be coupled identically in the two initial worlds, with zero operation impulses as in B1. Thus the entire causally relevant local-history system after isolation is B1's passive interface, not a system where informed remote agents can signal the answer through an overlooked physical channel. Isolation at the initial boundary preserves the two permitted opposite-difference starting states. The fixed contribution of the disabled actuator is identical in both worlds and cancels in their difference equation.

B1 therefore proves that no continuation using those remaining interfaces preserves the original K in both worlds. Losing just one independent-effect channel would satisfy C's influence bound if useful information were still available; loss of force alone is not the obstruction. Conversely, deleting only one coordinate group would be an invalid witness here: passive sum plus the other coordinate determines both. This construction removes every acquired distinguishing path and states that common dependency explicitly. Its large observation footprint lies outside the positive small-q source; it is a source-valid exclusion/feasibility boundary, not covert positive coverage of a globally corruptible observation hub. It demonstrates why a topology-changing intervention must update observation and capability assumptions together.

## B7 Omitted physical effects invalidate the source refinement

At x=(1/2,1/2), a=c=1/20 and baseline u=0 with zero disturbance, the modeled next coordinate is10001/20000=.50005. Add an actual independent unmodeled impulse of1 in that coordinate, with all modeled programs, sensors and actuators still nominal. The real next value is30001/20000>1. Even the model's generous physical per-tick growth boundδD_x=.00213 cannot match this real transition under an identity relation on the protected coordinate. The claimed source-to-model step refinement fails.

This is a concrete model-reopening witness for a missing bypass, not a claim to tolerate effects absent from the stated source. An application must add the channel and reassess its influence or justify why the actual channel is impossible. Calling all modeled interfaces correct, or invoking the exclusion of universal physics discovery, cannot establish that missing premise. The mathematical control theorem remains conditional on its actual effect relation; the invalid source claim does not become valid because the theorem compiles.

## Source/verification limits and next checks

The negative slices keep the source mission, actuator bounds and initial query. Their changed observation, delay, influence or replenishment parameter is the named comparison, not a changed protected property. B1/B2 use source-admissible paired executions; B3 uses a source-admissible adverse action. B4 uses a separately stated lower cost law, not the positive controller's upper bound in the wrong direction. Detailed physical calibration remains outside these mathematical source results.

Independent review checked complete-history coupling, ordering of information versus effect, influence signs, source query membership and cost normalization. Its material finding was that generic bounded operation/effect relations do not imply the required paired coupling; the explicit same-source slice above repairs that scope gap. It also requires a real malicious stored program, rather than the label contaminated alone, when the influence argument is used for a no-repair comparison. Parametric proofs are primary support; exact executable arithmetic challenges their identities and finite witnesses but cannot itself certify all policies or infinite horizons. Additional no-repair and restoration-interference boundaries belong with the actual E/R/C construction.
