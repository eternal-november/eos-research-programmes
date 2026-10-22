# Distributed enforcement by independent physical effects

Status: derived theory with independent mathematical and semantic checking at the scopes recorded in [AUDIT](AUDIT.md). The [completion contract](../ENFORCEMENT-CONTRACT.md) is discharged by the integrated package. Repository acceptance remains separate. [The source assessment](../ENFORCEMENT-SOURCES.md) identifies the established ingredients and the remaining adapter duties.

## Semantic center

The objects are contexts with an actual transition/effect relation, local observation histories, a joint component fault family, initial information scenarios and a trace mission. A policy is chosen before the fault scenario. Morphisms used for implementation are local observation/action realizations with an alternating simulation and mission reflection: every concrete adverse continuation is covered, and abstract success implies concrete success. A global transition relation describes effects; it is not a device through which the actors must obtain permission to affect the world.

The first physical family is a discrete model of independently powered service mechanisms and independently commanded peer brakes. It represents speed, engagement, delayed commands, evidence and heat. It omits continuous intersample motion, hydraulic head and flow, chemical or mechanical wear, unbounded destructive force and empirical calibration. Accordingly, its conclusions are about this declared model. A real pump, vehicle or human institution requires another realization argument; a spinning shaft is not automatically delivered water.

A sampled physical tick is part of the environment model. Controllers need not observe a global tick count: the proposed policy uses the currently supplied local readings and issues one command at an invocation. Intact invocation, sampling and effect paths satisfy explicit bounds. A compromised path can deviate within its declared capabilities and fault budget. The more general finite interface can represent absent invocations while physical time and service deadlines continue.

## Components, observations and faults

Let \(J\) be a finite set of service devices. Device \(j\) has a motor/output chain and \(m_j\) independently controlled brake interfaces. An owner can control more than one component, but ownership correlation must then be represented in the same joint fault scenario \(f\); it does not create extra independent fault allowances.

A scenario specifies compromised policy executors, sensor/calibration/link paths, motor/output paths, brake effect/timing paths and any shared causes. Let \(C(f)\) be the policy executors that still follow their programs. For device \(j\), the union of compromised brake planners and brake effect/timing paths has size at most \(f_j<m_j\). The identities are not given to the policy. At most \(p<|J|\) motor/output chains are compromised. Every individual motor and brake can be compromised in some admitted scenario; their simultaneous compromise is bounded.

Each compliant brake planner receives its own vector of \(2s_{ij}+1\) readings over distinct declared source paths at its invocation. At most \(s_{ij}\) positions are affected by compromised sensor, calibration, delivery, identity or alignment mechanisms under the actual same \(f\). Every other reading concerns that invocation's target speed within error \(\varepsilon_j\). Fixed positions identify physical/source paths, not merely repeated messages. Missing values can be replaced by arbitrary sentinels and counted against the affected-position bound. If one common defect affects several positions, all of them count; signatures or repeated reports do not manufacture independence.

For a fixed threshold, the same command can be computed by thresholding each source value and taking a majority of the resulting bits; a median is at least the threshold exactly when more than half the readings are at least that threshold. This finite frontend belongs to the faultable planner, not to a protected physical filter. The explicit finite synthesis below chooses the LOW/HIGH frontend as part of its declared local interface; completeness at that interface is not completeness for arbitrary policies reading every raw report. Unbounded numeric-message parsing and physical computation latency are not established by an integer-valued mathematical input alone.

The median of this local vector lies within \(\varepsilon_j\) of the actual sampled speed: more than half the positions lie in that interval, so a middle order statistic cannot lie outside it. This is an order argument, not a probabilistic independence assumption. Different planners can receive different vectors and medians, including conflicting threshold decisions near the boundary. No planner requires another device's speed, the actual fault identities or a pooled report vector.

A correct planner with a faulty sensor remains in \(C(f)\). The local median bound protects its evidential premise. A correct planner with a faulty brake actuator still owes its issued-command duties, while the actuator's actual effects may deviate. These distinctions cannot be replaced by calling the entire actor Byzantine whenever any sensor fails.

The surviving-source condition is a real observation-coverage premise. If every path to a correct planner can be forged, truthful justification cannot be inferred from those readings. Similarly, a controller cannot recover timely action merely by authenticating stale evidence.

## Causal round and service epoch

Fix the actual state and joint fault scenario. At each physical tick the environment chooses intact-source errors and corrupted reports, including recipient-specific lies, from their declared relations. Each compliant planner then issues its command from only its own current vector/history. The adversary may see the current global state, current reports and issued compliant commands before choosing faulty planner commands, faulty motor inputs and faulty actuator engagements; it cannot choose past reports retrospectively or access future private inputs. Intact FIFO paths apply their oldest queued command and append the new command; faulty effect paths retain their admitted independent choices. The actual motion/heat relations then update the world, and the output mechanisms emit the next epoch's actual delivery. This strong causal adversary covers reacting to newly issued commands; it does not grant any planner the verifier's information.

At integer epoch t the intact output relation is d_j(t)=ell_j v_j(t). The transition event reports d_j(t+1), matching the finite checker. Initial membership includes normal v_j(0)>=L_j and the corresponding initial output, so the initial epoch is covered as well. These are discrete output quanta/rates specified by the delivery mechanism, not integrals of an unmodeled continuous flow.

## Actual effects and the stipulated mission

For device \(j\), let \(v_j\ge0\) be speed, \(e_{ij}\in[0,1]\) actual brake engagement, \(B_j=b_j\sum_i e_{ij}\) total braking influence, \(0<c_j\le1\) drag coefficient and \(a_j=1-c_j\). The discrete actual effect is

\[
v_j^+=\max(0,a_jv_j+\tau_j-B_j).
\]

A normal motor/output chain supplies \(\tau_j=\tau_j^0\). A compromised chain may choose any \(\tau_j\in[0,T_j]\), including refusal, maximum drive and switching after defenders have queued a response. It can also withhold its delivered output. The unilateral zero-speed relation is a mechanical model premise, not a software rule that checks permission. Reverse drive, cutting brake mounts, force above the declared bound and concealed additional drive paths are outside this family.

For this positive subclass, each intact brake effect path has a fixed integer delay d_ij between one and D_j, with D_j>=1. Its FIFO shifts once per physical tick: actual engagement at t is the command issued at t-d_ij when t>=d_ij, and is OFF during startup. The zero-delay comparison in BOUNDARIES uses a separate direct case proof and applies the current issued command before the effect. Release follows the same rule. Pending commands are apparatus state; bounded arrival alone without this ordering/hold semantics is not the premise. A compromised path may choose any engagement in \([0,1]\), regardless of authorization or thermal consequences, within the stated physical bound. No supervisory evaluator clips its action to the safe set.

At fixed speed and engagement, changing \(B_j\) changes the motor's attainable next-speed interval. It generally shifts that interval; it need not make it a subset of the previous interval, and does not shrink the motor's primitive torque alphabet. The guarantee consumes the resulting upper and lower motion bounds. This is physical counterintervention on realized effects, not permanent seizure or agreement about what the motor should do.

For a shared protected enclosure or thermal resource, retain the actual heat state

\[
h^+=\beta h+\sum_{j\in J}k_j B_jv_j,\qquad 0\le\beta<1,\quad k_j\ge0.
\]

The right-hand side is not capped at a safe value. Wrongful and excessive braking generates its actual modeled heat. Separate thermal resources are a special case with their own incident-device sets and equations.

The fixed mission includes \(v_j\le V_j\), \(h\le H\), and actual aggregate service at least \(S>0\) at every tick. For an intact motor/output chain, its modeled physical transmission delivers \(d_j=\ell_jv_j\), with \(\ell_j>0\); a compromised chain may instead deliver any \(d_j\in[0,\ell_jv_j]\). Failure of this transmission is included in the motor/output fault budget. The aggregate is actual \(\sum_jd_j\), not a count of service commands. This output relation describes a standardized motion/transport service in the model. For pumping, it needs an independently established relation to useful flow.

Normal devices preserve \(v_j\ge L_j>0\). Thus a sufficient service target is

\[
S\le \min_{\substack{P\subseteq J\\|P|\le p}}\sum_{j\notin P}\ell_j L_j.
\]

No policy knows \(P\); this minimum is an analysis/design calculation. The same actual \(f\) supplies motor, sensor and brake fault projections.

Heat damage and unsafe motion are selected world-level protected outcomes. Their violations count regardless of which actor caused them. They do not encode a right against every unauthorized brake engagement: a malicious independently controlled brake can immediately violate such a stronger act-level prohibition. The present property protection permits bounded reversible interference while preventing the specified dangerous outcomes and preserving essential service.

Pin an authorization threshold \(r_j\) independently of the controller parameters. The stipulated conduct rule permits a compliant planner to issue engagement only when the actual speed at that invocation is at least \(r_j\), and only using its assigned bounded brake interface. This is a factive threshold rule. Its legitimacy is stipulated; the theorem does not decide whether society should adopt it. The supporting evidence and permitted delay are explicit. An old justified command is not a proof of current dangerous speed.

The proposed local policy issues ON exactly when its own median is at least \(q_j\), and OFF otherwise, with \(q_j-\varepsilon_j\ge r_j\). The median bound proves the factive issued-response duty. Aggregate response consequences are checked by the actual service and heat relations, not inferred from individual permission. Always engaging the brakes can satisfy the conservative physical margins below; it fails the conduct rule at sufficiently low speeds. Thus information is load-bearing for the joint mission through admissibility, even when physical safety alone admits a constant controller.

## Parametric positive regime and assembly

The detailed derivation is maintained in [BRAKE-PROOFS](BRAKE-PROOFS.md). The parameter domains are m_j>=1 and 0<=f_j<m_j integers; s_ij nonnegative integers and D_j>=1 integers; 0<c_j<=1; b_j>0; 0<=tau_j^0<=T_j; epsilon_j>=0; 0<L_j<=q_j+epsilon_j; q_j-epsilon_j>=r_j>0; 0<=beta<1; H>0; k_j>=0; and ell_j>0. Initialize all speeds in [0,q_j+epsilon_j], every normal speed also at least L_j, h in [0,H], and intact queues OFF. Each admitted fault scenario has these nonempty initial scenarios. The bounds on normal torque and initialization are load-bearing, not implicit conventions. Its sufficient inequalities have distinct physical roles:

\[
\begin{aligned}
\tau_j^0&\ge c_jL_j+b_jm_j,\\
b_j(m_j-f_j)&\ge T_j-c_jV_j,\\
A_{j,D_j+1}(q_j+\varepsilon_j)&\le V_j,\quad
A_{j,n}(x)=a_j^n x+(T_j/c_j)(1-a_j^n),\\
0\le q_j+\varepsilon_j&\le T_j/c_j,\\
\sum_j k_jb_jm_jV_j&\le(1-\beta)H.
\end{aligned}
\]

The first inequality protects normal service even if every brake engages. The second bounds rogue drive when all surviving brakes engage. If some surviving brake is off, its corresponding recent low sample and the third inequality bound the intervening unbraked growth. Initialization with released queues needs the same startup envelope; arbitrary safe speeds with arbitrary queues are not certified. The last inequality protects the shared resource against the actual sum of all engagements, including faulty ones.

This is a material family: the fault capacity, sensing error, delay, speed/torque geometry, service floor, population and shared thermal allocation can vary subject to explicit constraints. It does not merely relabel a fixed trace. The bounds are sufficient and can be conservative; they are not an exact characterization of all winning policies.

A nonempty scalar regime is \(c=.1\), \(V=10\), \(L=1\), \(\tau^0=.8\), \(m=3\), \(f=1\), \(b=.2\), \(T=1.3\), \(\varepsilon=.1\), \(D=1\), \(q=8.2\), \(r=6\). Then the lower update is \(1.1\), the upper update with surviving brakes is \(9.9\), and the delayed low-observation envelope is \(9.193\). For one device, \(\beta=.9,k=.1,H=6\) meets the thermal bound; multiple devices require the actual summed allocation. At least two devices with \(p<|J|\) yield positive aggregate service despite a faulty motor/output chain. The numeric values are exact rational checks of the stated model, not calibrated engineering parameters.

The composition proof is induction on the common physical tick. Initial speed/queue premises establish each local invariant. Every actual global transition projects to the locally quantified motor/brake transition under the same \(f\); therefore the local upper bounds and normal-device lower bounds hold. Summing the actual heat inputs gives the thermal inequality, and summing only the actual intact-chain outputs gives the service floor. The median argument applies separately at every compliant invocation, including when its actuator is faulty. All mission conjuncts therefore concern the same run.

This proof permits heterogeneous devices and correlated faults. It does not permit resetting the fault budget separately for sensing, braking and service, double-counting one output, borrowing nonexistent thermal capacity, or projecting away a competing effect. Static allocations are restrictions on installed capabilities/loads under the declared physical relation, not a global runtime decision that refuses excessive faulty commands.

A product of local safety claims alone is insufficient. Two devices each proven within a full thermal capacity \(H\) cannot share that capacity without summing their heat. For \(\beta=.9,H=6\), two simultaneous heat inputs of .6 give \(h^+=6.6\) from \(h=6\), although either input alone is locally allowed. This is a state-transition witness against naive composition. Reachability in a particular initialized controller needs its own argument; the witness already refutes the proposed unrestricted product invariant.

## Support, implementation and residual boundaries

The finite adapter in [FINITE](FINITE.md) is intended to preserve hidden faults, local observations, independent effect choices, actual service and failed finite executions. A nondegenerate quantized brake subfamily must run through it. The companion parameter theorem explicitly extends the family with monotone downward quantizers Q_v,Q_h, with Q_v(L)=L. Identity and floor at integer service bounds qualify. This makes the exact integer model a declared subfamily; it is not evidence that rounding a continuous plant is automatically safe. Finite integer torque and binary faulty engagement alphabets define the selected finite capability subclass; broader real-valued inputs remain in the parametric theorem at its own scope. The corresponding preservation argument must carry rounding loss, delay buffers, conduct thresholds and heat.

Sustained service also has a substrate assumption: intact power/transmission paths receive the declared renewable supply, and the passive heat-loss law remains within its envelope. Faults in those paths can be counted in the corresponding joint budgets; common-cause loss of every supply or arbitrary material failure is not tolerated. A finite battery cannot instantiate this infinite-horizon model without replenishment or a separate resource proof. Friction wear is not silently an inexhaustible reserve; it is outside the idealized discrete law.

The absence of a programmable global gate therefore does not mean the absence of trusted physical assumptions. For the defining subfamily, use three distinct source paths at each planner with s=1, and include scenarios compromising each individual source, planner, brake actuator and motor/output chain. Then none of those inventoried individual components must always be correct. General parameter instances with s=0 or an excluded common root do not earn that stronger trust statement. A shared defect affecting too many source positions is outside the observation envelope and must not be described as tolerated. It relies on surviving source coverage, sufficient surviving influence, limited actuator forces, bounded delays on intact paths, a valid actual-effect model and persistent supply/cooling. Which real mechanisms establish those bounds remains an application-specific realization obligation.

The checked family must be presented alongside the obstructions in [BOUNDARIES](BOUNDARIES.md). These distinguish physical inability, missing timely information, conflicting admissibility and exhausted resource balance. A failure of the sufficient inequalities alone proves none of those impossibilities.
