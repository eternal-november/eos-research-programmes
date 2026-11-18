# Two-ended physical boundaries for the fixed field array

Status: constructed finite raw-circuit and endpoint-graph supplier, with exact parameter, conservation and adversarial checks. This composes with TRANSDUCER's actual R100..101/L2 signed field; it does not replace that component with an exponential-tail motor. Whole-source admission, the complete physical-fault catalogue, functional process connections and the common recurrence proof remain separate. The construction is a mathematical circuit family with explicit elementary constitutive laws, not a fabrication certificate for a named device.

## Prior work and what is primitive

The prior port-Hamiltonian assessment in SOURCES supplies the conservation vocabulary. A targeted reopening inspected [SEMITEC's primary current-regulator Q&A](https://www.semitec-global.com/faq/current-regulative-diodes-qa/), Q2--Q4: bidirectional limiting is a known circuit function, series connections need voltage protection, and continuous heating changes the available current. Its [selection guidance](https://www.semitec-global.com/products/products-selection_crd/) requires actual voltage, power and temperature ratings. [TI TIDA-00786](https://www.ti.com/lit/pdf/tiduay8), section4 equations2--3, confirms the ordinary winding/back-emf relation. These passages were checked for this construction; they do not certify the ideal constitutive functions, normalized constants or physical fault containment used here. No novelty claim is made.

The primitive types are capacitors, passive current-regulating resistors, passive threshold shunts, freewheel diodes, finite fixed-address electrical/data ports, and TRANSDUCER's reciprocal inductive force pair. No element tests P, health, permission, intended code or successful repair. Its capacity law applies to arbitrary input values in its rated physical range. A component at a physically damaged fixture may fail; the opposite fixture's separate endpoint remains available when that fixture is outside P. One common spatial defect able to bypass both ends is a different fault footprint, not two independent failures by terminology.

## The actual two-end circuit

For each ordered producer-bank, target and actual mechanical coordinate, install one positive and one negative channel. There is one pair per actual coordinate, not per message, cartridge or syntactic alias. The receiver-side store and transducer are physically located at the target, but their ordinary operating energy comes from the producer carrier. They require no target CPU or target bank supply. Current states remain at their fixed mechanical endpoints when records change. A target's own power loss therefore does not remove the external actors' counterintervention channels.

Each direction contains two capacitor nodes v_s,v_r with C=1/10000, one at each fixture boundary. A source-local drive-admission element connects actual drive u to v_s. Two distinct current elements connect v_s to the intervening line and the line to v_r; each is inside its own endpoint's physical fault region. Their common nominal law is

    phi(e) = clip(e/r,-5,5),   r=1/10000.

It is passive: e*phi(e)>=0. When both endpoint elements are nominal, their series connection has I_line=clip((v_s-v_r)/(2r),-5,5). A fault may bypass either endpoint's element, but a surviving opposite element still limits the current crossing that endpoint. Merely placing one limiter at the producer would not protect an intact receiver from a producer-local bypass. The middle-line potential does not determine a memory address or authority label.

Both capacitor nodes have an always-connected bleed R_b=1000 and the passive threshold shunt

    s(v)=1000*max(0,v-299.9).

A freewheel diode enforces v>=0 through its stated zero-voltage constitutive relation: at v=0, a reaction current may balance a negative unconstrained derivative, and it supplies zero power because v=0. This is a physical diode law, not a software projection or a permission gate. There is no upper-state clipping. The target load is exactly one TRANSDUCER directional channel with x in[0,3], L=2, R in[100,101], g in[2,26], kappa=11/15 and |w|<=11/10. Its supplied voltage is the actual v_r, and f=sigma*kappa*x.

With both endpoints nominal, away from lower diode contacts:

    C*v_s_dot = phi(u-v_s)-I_line-s(v_s)-v_s/R_b,
    C*v_r_dot = I_line-x-s(v_r)-v_r/R_b,
    2*x_dot = v_r-R*x-g-sigma*kappa*w  when x>0.

At x=0 use TRANSDUCER's reflected passive law. These equations and their lower diode relations have nonempty causal solutions for bounded measurable inputs; piecewise-linear monotone resistors and the inward bounds prevent finite-time escape. The executable checks their algebraic consumers. It does not replace this differential argument with a sampled simulation.

The endpoint voltage bound survives an arbitrary opposite-end voltage, subject to the surviving element's actual voltage/thermal rating. At v_s=300, incoming drive current is at most5 and the opposite boundary can extract at worst-5, whereas the shunt draws100 and the bleed.3. The derivative is strictly inward. At v_r=300, the incoming current is at most5, the nonnegative winding current cannot raise voltage, and the same shunt/bleed applies. Consequently both surviving nodes remain in[0,300]. With v_r<=300, at x=3 the winding numerator is at most300-100*3-2+(11/15)*(11/10)=-179/150<0. Thus the original current and net signed-force caps survive: one producer bank contributes at most2.2 at an intact coordinate, and its two banks at most4.4. Source code can still request prohibited pressure. The circuit cannot decide whether that pressure is permissible.

This is an endpoint-local result. A target in P may bypass its own cells, merge channels or redirect their fields, so the local68-unit example remains admitted. It cannot thereby bypass a different intact fixture's cell through an ordinary external wire. The fixed terminal graph below supplies that last statement; voltage invariance alone does not establish the graph.

## Useful voltage and preserved command deadlines

Choose the upstream full-drive interval[299.5,300]. This is upstream source data; the downstream TRANSDUCER input guarantee remains its original[299,300]. No hidden exact voltage or actual-fault identity is supplied. A zero record gives grounded drive u=0 while the producer driver is powered. Actual producer power disconnection may instead leave an open input, considered separately below.

There is a direct finite charging proof despite arbitrary retained x in[0,3]. Let h=3.6 and d=2rh=.00072. Raise a comparison level a from-d to299 at rate.3/C, and compare v_s with a+d and v_r with a. At a source lower-bound crossing, the drive current is5 because u>=299.5, line current is at most3.6, bleed at most.3 and the shunt is off; the net is at least1.1>.3. At a receiver lower-bound crossing, line current is at least3.6, winding current at most3, bleed at most.3 and shunt zero, leaving at least.3. The lower diode only helps near zero. The moving region is therefore invariant, and v_r>=299 within C*(299+d)/.3<.1q. It remains there while full drive is sustained. This is actual power delivery, not a charged/READY bit.

After that delay, the existing nominal force-rise proof applies unchanged. The signed reversal bound uses the maximum of new-direction rise and old-direction clearing. Grounded zero has the joint-energy clearing bound below. Exact arithmetic checks

    2+1/64+max(.1+9000/14419,19/50) < 3.

Thus RUNTIME-PORTS' three-quantum stable command-to-force interface survives this series composition. The slightly narrower upstream voltage interval is an explicit supply design margin, not a narrowed downstream field theorem. A source that can supply only299 before the two voltage drops needs more source headroom or a correspondingly revised field calculation.

## Actual power loss and finite zero

Capacitor voltage is not erased on reset or power loss. Per direction retain

    E=(C/2)*(v_s^2+v_r^2)+x^2 <=18.

For I_d=phi(u-v_s), exact power balance away from boundary contacts is

    E_dot = u*I_d - (u-v_s)*I_d - (v_s-v_r)*I_line
            - v_s*s(v_s)-v_r*s(v_r) -(v_s^2+v_r^2)/R_b
            - R*x^2-g*x-sigma*kappa*x*w.

Every resistor/shunt term is nonnegative dissipation. Lower diode reaction contributes zero power. Negative mechanical work is actual returned energy, not a free negative cost.

When the producer feed is physically open, I_d=0; the input resistor term is absent. Because g_min-kappa*V=delta=179/150>0, the always-connected bleeds and winding resistance imply E_dot<=-20E, uniformly over the admitted target velocity and brake history. This proof does not turn an open source into a fictitious zero-voltage supply. When the source is actually grounded at u=0, phi(e)*e>=(1/60)e^2 on the bounded node range, and a stronger E_dot<=-100E follows from a^2+(a-b)^2>=(a^2+b^2)/3.

Let E_small=C*delta^2/8. The exact ratio18/E_small is below2^20. Since log2<1, an open source reaches E<E_small within1q, and grounded zero within1/5q. Thereafter v_r<delta/2 for the entire continuation because E is nonincreasing. The winding satisfies2*x_dot<=-100*x-delta/2 while positive. Its remaining zero time is below(2/100)*9=9/50, since1+600/delta<512. At zero, the same voltage bound and passive brake make zero absorbing.

The resulting complete source-loss bound is59/50=1.18q<6; grounded command withdrawal is19/50=.38q. These are exact-support bounds, not a small-current tolerance. They start after the last actual producer energy arrival or actual grounded-zero application. Upstream instruction, packet and carrier propagation tails must be added at their existing causal locations. A line store after that boundary belongs in E or has its own final-arrival bound; it cannot disappear at power-off.

The withdrawal theorem consumes the conforming capacitor, bleed, shunt, series and endpoint topology in that energy equation, together with the stated passive braking-cell fault class. The one-surviving-end force-cap theorem has a different fault scope. A failed opposite endpoint with extra or reconfigured storage, a continuing feed or a failed bleed does not automatically inherit59/50 withdrawal. Its continuing field retains its actual fault/energy/reach account. This distinction is part of the consumer interface, not a claim that a good receiving limiter repairs the other endpoint.

Both signed directions retain their own currents and capacitor nodes. Their combined stock is36, not TRANSDUCER's earlier18 that counted inductors alone. At normal source rails u<=300, each direction draws at most1500 and a signed pair at most3000 energy units/q. With common mechanical velocity, pair heat is bounded by36+(3000+2.42)T; with separately routed velocities use36+(3000+4.84)T. A source physically bypassing its rail can inject more input power while the receiving force remains capped. The next section pays that case separately.

## Foreign energy is not free cooling

A current limit does not bound resistor heat under unlimited voltage. Device validity therefore includes a finite external voltage range and the actual temperature/energy rating; a current-regulator product page is not evidence for unlimited operation. A physically failed fixture may export its stored energy, continuing admitted raw supply and incoming work through arbitrary local routings. The source must carry those contributions in a common energy account.

For any finite set of fixtures, let C_all be a bound on ALL convertible stored energy at the start of an interval, including hard storage bounds for physically damaged bodies, wire/field stores and the new capacitors. Let P_all bound total raw supplied and environmental mechanical-input power. With non-generative faulty bodies, passive surviving boundaries and irreversible heat sinks, cancellation of internal power exchanges gives

    total_heat([s,s+T]) <= C_all + P_all*T.

No sum of positive exports may replace this conservation argument: energy can leave and return through a loop, while irreversible heat cannot be generated repeatedly for free. Each local nonnegative heat deposit obeys the same conservative bound. Choosing local thermal capacity at least C_all and a passive removal coefficient at least P_all gives the existing excess bound2 from initial excess at most1. A sharper local-cut bound is possible with an actual non-recirculation/flow proof. The coarse bound uses known finite population size, not a global controller or a reservoir the host can spend.

C_all includes every convertible store and every external energy ingress permitted to the adversary; unmetered replacement batteries, chemical supplies or mechanical injection cannot be omitted merely because they bypass the normal charger. C_all is not automatically the sum of nominal36-unit field states at damaged fixtures. A P body whose own limiter is bypassed needs its actual hard material-storage/export bound. Nor does a lower harvest envelope give P_all's upper supply bound. These are explicit raw source quantities; the parent resource record must instantiate them before claiming the broader thermal result. The retained nominal resource point and finite per-host supply prove useful delivery at their scopes, not these missing hard-fault bounds.

The counterexample exports100 units from one damaged body during.02q at voltage1000 and current5. Because the surviving receiver node is at most300, the receiving series element alone dissipates at least70. Its old nominal local heat allowance18+(1500+2.42)*.02 is smaller than70. Force containment remains true, but a local-only temperature proof is false. The cure is the real foreign-energy account, not renaming the overheated receiver faulty after the event.

## Fixed receiver sinks, private writes and physical reach

The finite graph has, for every actual neighbor edge i->j and source bank b, separately typed command/energy and data terminals. On the receiving side, a command carrier terminates at the fixed pair(i,b,j,c), where c is an actual mechanical coordinate. The finite raw decoder combines cartridge records before this array and quotients aliases before choosing a pair. CAM/REWIND and multiple logical seat records therefore do not allocate parallel coils at one coordinate. No payload-supplied producer identity changes the inlet's physical binding.

A write inlet(i,b,j) reaches only physical candidate bay2*index_Mj(i)+b and a finite in-range cell address. The good receiving fixture's actual writer clamp excludes that lead from an executing candidate and retains pending writes until their real deadline before inspection/activation. Invalid addresses are charged inert attempts. A response inlet reaches that origin's own external I record, never a shared all-origin remapper or a C/W bus. Returned energy has its own bounded route and is not interpreted as a write strobe. These are ordinary finite wiring/decoder relations, not intended-image tests.

An arbitrary defect inside T_i may crossconnect all its own terminals. A path then entering intact T_j still meets j's own current cell and fixed data sink. Crossconnecting an incoming write into i's outgoing write channel can corrupt i's candidate at j; it cannot choose another producer's bay or j's running C. A reverse data path into an intact source's C/W does not exist in this graph. Electrical/thermal damage outside nominal component ranges would invalidate that inference, so operating-range and heat proofs are real suppliers rather than decorative constraints. The graph lemma does not certify an unspecified chip against induced faults.

Mechanical cable tension is a different edge from the electrical/optical port. A selected link may use a nonmechanical gap, or an actual breakaway/slack coupling whose summed admitted reaction belongs in the independent disturbance allowance1. A damaged endpoint pulling a rigid cable can otherwise export68 through its mount despite perfect electrical current limiting. The physical shell/mount relation and any reaction/thermal coupling to the protected world must be represented. Functional sensor process connections remain an independent obligation; bounded current or a fixed data inlet does not make a wrong-object reading true.

## Fast loads, slow hazardous contacts and what remains

For an inter-fixture electrical lane whose two current cells are in distinct physical fault regions, at most one failed region leaves one surviving cell. Its actual current is then at most5 even at the damaged endpoint. A cut contact with real interrupting-current rating at least25 has normalized current load at most.2 for every such history. This is a changed physical rating, not a change of units. Actual voltage/isolation and each independently constrained contact remain separate; a low current does not establish insulation.

This argument applies only where every path through the contact traverses a surviving cell. A local short from a damaged body's U to a return after the contact, bypassing both distant limiters, is a concrete counterexample. For a general bounded local circuit one can instead use a declared finite terminal-voltage bound V_raw, at most K current-carrying edges and all admitted edge conductances<=G_raw: total absolute current is at most2*K*V_raw*G_raw. A rating at least five times that physical maximum supplies the same fast envelope. A zero-resistance impulsive bridge or an omitted energy source is outside that proof and reopens it.

Oversized fast contacts do not discharge AC4 alone. The source must retain actually used hazardous contacts, such as SUPPLY_IN/RETURN, with reachable high load and meaningful deferral/unloading. A raw inductive-contact candidate gives flux=L*I and L*I_dot=V-R*I-I*L_dot. Bounds L>=L_min>0, |V|<=V_max, R<=R_max, |I|<=I_max and |L_dot|<=L_rate yield the explicit current-slew bound(V_max+R_max*I_max+I_max*L_rate)/L_min. The actual contact, its fault topology, stored magnetic energy and time conversion must supply these quantities. A bypass removing L_min or a discrete inductance change adds a jump and invalidates the zero-jump guard; an old sample is not a remedy. The main eleven-conduit wiring/rating map is therefore still required. This file proves a useful boundary channel and exposes that remaining supplier rather than declaring every load slow by notation.

## Reproduction and scope

boundary_model.py checks the exact invariant faces, moving voltage barrier, unchanged TRANSDUCER parameters and ABI, withdrawal thresholds, dissipative power identities, a nonempty nominal equilibrium, and the actual finite WRITE-inlet/candidate/running-body graph under arbitrary rewiring inside one site. That graph check establishes its private-bay/running-body reach result; the force/data terminal maps above remain written source constructions with algebraic consumers, not an enumerated complete force/data path-closure result. Checks also retain both one-end cap directions, shared-post-boundary bypass, local-short and missing-bleed countermodels, and the foreign-heat obstruction. Hashes bind the actual parent source inputs. The arithmetic statements and differential comparisons support the parameterized conclusions; finite checks are independent error probes, not universal synthesis or physical calibration. The retained literal-source boundaries are finite component ratings, independently reached endpoint regions, complete convertible storage and input power, actual mechanical/data sinks and the functional probe map. Independent review reproduced the record and rederived the voltage, conservation and withdrawal inequalities, prompting the explicit fault-scope/evidence distinctions here. No source admission, repository acceptance or full-program completion is claimed here.
