# Feasibility boundaries under the same actual-effect semantics

Status: derived arguments and exact witnesses, independently checked at the scopes recorded in AUDIT.md. These results complement the positive family in [THEORY](THEORY.md); they do not turn failure of a sufficient condition into a universal impossibility claim. All normative thresholds below are fixed independently of controller and observation parameters. The real-valued authority, timing, heat/speed and persistent-heat arguments in this file use identity quantization and the displayed exact effect relations. They do not automatically transfer to arbitrary downward quantizers, which need not preserve lower bounds; the finite floor subclass has its separately checked boundaries in FINITE.

## Physical authority: a policy-independent cut

Consider one compromised motor with \(0<c\le1\), \(a=1-c\), maximum input \(T\), speed limit \(V\), and at most \(\bar B\) total braking influence available from all nonfaulty mechanisms. Select an admitted fixed fault scenario in which the remaining faulty brakes exert zero influence. Suppose

\[
T-\bar B>cV.
\]

Let the adversary keep the motor at \(T\). Every policy, including a full-information centralized policy, then satisfies

\[
v_{t+1}\ge av_t+T-\bar B.
\]

The right side is positive for \(v_t\ge0\), so the unilateral relation cannot invalidate the inequality. Induction gives

\[
v_t\ge a^tv_0+\frac{T-\bar B}{c}(1-a^t).
\]

For \(0<c<1\), the lower bound converges to a value strictly larger than \(V\), and crosses \(V\) after finitely many ticks from any initial \(v_0\in[0,V]\). For \(c=1\), the violation occurs in one tick. Thus no policy preserves the speed constraint in that capability context. Unused information, authentication and agreement cannot increase \(\bar B\).

For homogeneous brakes, \(\bar B=b(m-f)\) when the admitted scenario compromises exactly \(f\) effect paths and those paths refuse. This is one fixed joint fault scenario, not a new faulty set selected at each tick. The conclusion requires that the model has no other counterintervention path such as cutting power or evacuation; adding one changes the capability context and reopens the question.

At the numeric regime \(c=.1,V=10,T=1.3\), two surviving brakes of strength .1 give \(\bar B=.2\), whose equilibrium lower bound is \(11>10\). Two brakes of strength .2 instead meet the positive authority margin. This is a comparison of physical capability with mission, sensing and other dynamics fixed. It does not prove that every failure of the positive construction's more conservative inequalities is losing.

## Information: a legal response needs a timely distinction

Fix the actual joint fault scenario, the compliant planners and their private initial information. One target motor is compromised; other healthy devices continue to supply the required service. The target has two possible initial speeds, \(v_{\rm low}=1\) and \(v_{\rm high}=10\). The authorization threshold is fixed at \(r=6\), and a compliant planner may issue a positive engagement only when the speed at that invocation is at least \(r\). The motor capability remains \(T=1.3\), \(c=.1\), and the upper limit is \(V=10\). Before the first physical effect, the available actions are the modeled engagement commands; no distinguishing side channel or probe completes in that interval.

Set engagement delay to zero in both observation contexts. In the inferior context, each intact source has a nominal coarse observation map that returns the same constant symbol before the deadline, regardless of target speed; no allowed probe or communication supplies a finer distinction. Corruption identities and budgets are unchanged relative to that nominal interface. This changes observation coverage, rather than silently corrupting all source paths while claiming the original majority-error bound. Thus all compliant actors receive identical local initial histories in the two worlds. Any deterministic local family issues the same commands in both. In the low world, the fixed response rule requires every compliant brake command to be OFF. Select the admitted faulty-brake behavior OFF as well. Therefore the high world also has no braking and

\[
v_1=.9(10)+1.3=10.3>10.
\]

No deterministic local policy can satisfy the joint mission in both initial worlds. Use the same joint law of honest private randomness in both scenarios. The same conclusion holds for probability-one randomized success: legality in the low world forces zero probability of positive compliant engagement there; identical joint honest intervention laws force the same distribution in the high world. This is an application of the coupling obstruction under matched fault scenario and causal information, not an argument from equal individual marginals.

In the corresponding informative context, intact local source majorities provide error at most .1 before the effect, and the brakes have zero delay. The threshold \(q=8.2\) distinguishes these worlds and satisfies \(q-\varepsilon\ge r\). The direct ON/OFF case split proves invariance from arbitrary initial target speeds in \([0,V]\): all surviving brakes ON give the authority bound; some surviving brake OFF gives \(v<q+\varepsilon\), hence \(v^+\le .9(8.3)+1.3=8.77\). Normal service and the thermal allocation are unchanged. Thus this pair of contexts changes only observation coverage, with the same mission, fault family, primitive effect capabilities and initial physical worlds.

The separation is about the joint mission. Under the conservative positive-family margins, constant ON can preserve physical speed, heat and service. It is ruled out by justified-response admissibility at low speed. That is a substantive information requirement, not a claim that sensing is always necessary for pure physical safety.

Adding an inspection restores this particular distinction only if its sound result reaches the relevant planners before their intervention deadline. It does not by itself prove sufficient authority or admissibility in another state.

## Timing: knowledge can arrive before the device can act

Hold the informative observation context and physical parameters fixed, and initialize \(v_0=V=10\) with actual engagements and pending queues OFF. With zero engagement delay, the threshold policy can react before the first effect as above. With one tick of unavoidable engagement delay, every policy has \(B_0=0\), even if it knows the true speed and every faulty identity. The same admitted motor action produces \(v_1=10.3\).

This is a policy-independent deadline obstruction for that initial information/apparatus family. It does not refute the positive one-tick-delay theorem, whose initialization leaves headroom and constrains queues.

More generally, if no brake can affect the target during the first \(D\) ticks and the rogue motor can maintain \(T\), then

\[
v_D=A_D(v_0)
\]

under zero braking. Whenever \(A_D(v_0)>V\), violation occurs by that deadline. This is a necessary initial-headroom condition for that actual startup arrangement. The positive recent-evidence condition \(A_{D+1}(q+\varepsilon)\le V\) is a separate sufficient condition for continued operation.

## Physical power versus joint admissibility

At a state \(v=V\), \(h=H\), consider a rogue motor at \(T\) and a total actual braking influence \(B\). One-step speed protection requires

\[
B\ge T-cV.
\]

For one device contributing heat \(kBv\), thermal protection requires

\[
B\le \frac{(1-\beta)H}{kV}
\]

when \(kV>0\). If the lower bound exceeds the upper bound, no action meets both constraints, even if physically available braking exceeds the speed requirement and every defender has perfect information. The forbidden high-force transition remains in the actual plant; the mission rejects its heat consequence.

For example, keep \(c=.1,V=10,T=1.3,k=.1,\beta=.9\), and take \(h=H=1\). Speed requires \(B\ge .3\), but protection of the thermal state requires \(B\le .1\). Available force .4 is physically effective against the rogue drive: it gives next speed \(9.9\). It also gives next heat \(1.3>1\). This is an explicit powerful response excluded by the joint mission, not an administrative permission flag.

The obstruction applies to initial/reachable states containing this \((V,H)\) pair. It does not establish that every lower-heat initial state with the same hardware is losing; a controller may preserve reserve. The positive-family allocation deliberately excludes this insufficient-cooling regime.

## Persistent malicious enforcement and resource balance

Suppose a protected shared heat state satisfies

\[
h_{t+1}\ge\beta h_t+Q,\qquad 0\le\beta<1,
\]

under one chosen admitted persistent adversary on every policy/run meeting the required service floor, because a fixed admitted set of faulty brakes can maintain a heat contribution at least \(Q>0\). If \(Q>(1-\beta)H\), indefinite thermal protection is impossible. Iteration gives

\[
h_t\ge\beta^th_0+\frac{Q}{1-\beta}(1-\beta^t),
\]

which eventually exceeds \(H\). In the brake model one sufficient source of such a lower bound is a service-protected device with speed at least \(L\) under persistent hostile force \(b_F\), giving \(Q=kLb_F\). For an aggregate service specification, derive the corresponding lower bound from the actual service allocation rather than assuming a particular target must remain active.

A concrete instance uses two devices with the real speed/service parameters in THEORY and shared H=12 and delivery coefficients ell_1=ell_2=1. Fix one motor/output chain faulty and withholding all service, and one brake effect path on the other, intact chain faulty and persistently ON. These roles are projections of one admitted fixed scenario. The required aggregate service is at least one, so any successful run has the intact device speed at least one; its unavoidable heat input is at least k*b*L=.02. Change only thermal retention from beta=.9 to beta=.999. Then (1-beta)H=.012<.02. Starting at h0=0, the lower-bound recurrence crosses12 at tick916. Sensor identities, mechanical capabilities, service requirement, initial family and protected heat limit are unchanged. The lower-bound trace is a proof witness; actual heating can be larger and failure earlier.

This is an impossibility of the conjunction: reducing speed below the service requirement to avoid heat is not a successful controller. A genuine mechanism that releases hostile force, changes cooling, reallocates delivered service or replenishes an exhausted resource changes the context and may remove the obstruction. A monitor that silently suppresses the hostile force does not.

## Protected outcomes and prohibited acts are different

If the stronger mission forbids every unauthorized brake engagement, an independently controlled faulty brake can violate it immediately whenever that engagement is physically available and no mechanism prevents it. The positive family's theorem does not satisfy that stronger mission; it protects selected actual outcomes and constrains compliant issued responses.

Likewise, proof that a brake's force stays below a material bound does not protect every property interest. Thermal damage, lost essential service and dangerous motion are the declared world-level protections. Seizure, wear, property title and broader legitimacy require their own state, capability and normative interfaces if claimed.

## Comparisons and verification duties

These witnesses keep the actual adverse effects visible and state whether the conclusion concerns every policy or a chosen policy. The physical-authority, blind-information, initial-delay, one-step heat/speed conflict and persistent-heat arguments are policy-independent in their declared contexts. Removing the peer-brake channel and finding an overspeed trace is a construction ablation; by itself it does not characterize every other architecture.

Executable checks should reproduce the numeric witnesses with exact arithmetic, exercise the same actual-effect code where the models coincide, and reject mutations that erase hostile actions or change the authorization threshold with the sensor/controller design. General convergence and indistinguishability arguments remain proof obligations; a finite run alone does not establish their quantified conclusions.
