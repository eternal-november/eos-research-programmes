# Source-level information, influence and resource boundaries

Status: coordinator derivations awaiting independent mathematical/source checking. These answer named negative questions in [SOURCE](SOURCE.md); they do not replace its required positive construction. The proofs use ordinary indistinguishability, linear dynamics and cumulative accounting. No novelty is claimed. Reconstruction impossibility, control impossibility and failure of a chosen sufficient certificate remain separate.

## B1 Passive evidence cannot preserve this mission

Consider the fixed passive-sum ablation from SOURCE. No raw heterogeneous measurement becomes available without acquisition; the compared policy has no such acquisition interface. All local plant observations are functions of x₁+x₂, and every other observed datum, initial local memory, scheduling/availability relation and source effect queue can be chosen identically in the paired executions. The same actuator command and queue outcome produces the same additive input in both worlds. Ordinary repair may change stored program state but reveals no extra plant coordinate in this ablation. No faults are necessary for the obstruction: the no-fault, zero-disturbance scenario is admitted. The controller is any deterministic family based on permitted histories, with arbitrary memory and communication.

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

## Source/verification limits and next checks

The negative slices keep the source mission, actuator bounds and initial query. Their changed observation, delay, influence or replenishment parameter is the named comparison, not a changed protected property. B1/B2 use source-admissible paired executions; B3 uses a source-admissible adverse action. B4 uses a separately stated lower cost law, not the positive controller's upper bound in the wrong direction. Detailed physical calibration remains outside these mathematical source results.

Pending independent review must check complete-history coupling, ordering of information versus effect, the legitimacy of the zero-disturbance slices, the repair/access distinction, source query membership and the cost normalization. Parametric proofs are primary support; exact executable arithmetic can challenge their identities and finite witnesses but cannot itself certify all policies or infinite horizons. Additional no-repair and restoration-interference boundaries belong with the actual E/R/C construction, rather than being invented here before its source mechanism is fixed.
