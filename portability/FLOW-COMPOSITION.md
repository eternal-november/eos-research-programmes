# Common flow and event continuation for a finite source

Status: derived restricted composition theorem, independently reviewed at its stated abstract interface after boundary/input-scope repairs; complete source inventories remain open. It factors the time/nonblocking part of [CORE](CORE.md) using the existing [FLOW-EXISTENCE](../local-control/FLOW-EXISTENCE.md) construction. Source-specific coordinate/port and event certificates remain necessary. This theorem does not imply useful repair, safety or a population-uniform cost bound.

## State and port composition

Fix one finite roster and a held-request mode mu. Retain all independent physical storage coordinates in y in R^n. Actual material stops/diodes form a fixed product of closed intervals D. The protected world variables are unrestricted in D: their desired safety region is not a fictitious flow constraint. Let J name unrestricted coordinates with scalar passive Sign brakes.

A local component supplies fixed linear coordinate selection S_i and derivative injection P_i, constitutive f_i, algebraic ports a_i and their bounds, uniformly over the admitted bounded input values. The port certificate explicitly parameterizes the actual interconnection as a=A_mu(t,y,w). It establishes both satisfaction and coverage of admitted cases; choosing one favorable algebraic solution does not cover a demonic source. Remaining choices w must be the source's actual bounded measurable inputs under the stated causal interface. Arbitrary instantaneous state-feedback choices require their own regularity/closed-loop existence law; finite-rate held requests cannot be replaced by discontinuous algebraic adversarial feedback.

For example, M_mu(t,y)*a=r_mu(t,y,w), with invertible M, is a sufficient finite certificate. If ||M^-1||<=kappa, ||r||<=R, Lip_y(r)<=L_r and Lip_y(M)<=L_M on a compact time/state cylinder, then

    Lip_y(A_mu) <= kappa*L_r + kappa^2*L_M*R.

Subtract the inverse equations and use M(y)^-1-M(z)^-1=M(y)^-1*(M(z)-M(y))*M(z)^-1 to obtain the bound. An underdetermined relation may instead retain its actual free port variables. Nonsingularity is a convenient sufficient construction, not a universal restriction on every legitimate interconnection.

After substitution, the certificate must establish the exact evolution form

    y' + n + sum_(j in J) b_j(t,y)*xi_j*e_j = f(t,y),
    n in N_D(y), xi_j in Sign(y_j), b_j >= 0.

For f=sum_i P_i*f_i(t,S_i*y,A_i(t,y,w)), finite-sum composition gives a conservative local Lipschitz constant sum_i ||P_i||*L_i*(||S_i||+Lip(A_i)). Measurability and compact-cylinder boundedness are preserved. Nonnegative brakes on the same coordinate sum to a coefficient times the same Sign graph; arbitrary transformed-coordinate brakes are not covered by that step. Linear growth passes through appropriately bounded local maps, or independent physical storage/comparison laws supply the finite-horizon envelope required by FLOW-EXISTENCE.

For a fixed held mode and the same chosen admissible measurable input w, the imported finite-dimensional normal-cone/Sign construction gives an absolutely continuous trajectory and its stated retained-state uniqueness. Different admissible nondeterministic input/port choices may produce different state trajectories and are not identified by this uniqueness statement. The uniqueness coefficient is bounded by L_f+sum_j L_bj. It does not grant uniqueness of underdetermined eliminated ports. Mode changes retain actual storage and use compatible initial data.

This is a real restriction. Eliminating retained state can turn product stops into coupled constraints and off-diagonal reactions, outside the imported theorem. Power conservation does not restore the missing form. Contradictory ideal voltage sources illustrate that separately meaningful components can have no compatible port solution. An adapter must preserve the displayed form or justify a different evolution result; neither a diagram nor a whole-system `nonblocking` predicate is a substitute.

## Event inventory and finite concatenation

Separate independently counted roots from descendants. For each actual root channel c require N_c([0,T])<=sigma_c+lambda_c*T with finite constants for the fixed roster. Roots include hardware instruction/request launches, raw ingress/direct strobes and held physical/parameter updates. Continuing malicious actions through already possessed authority are counted by those hardware channels; they are not mislabeled fresh acquisitions. Let R(T) be the sum and P0 the finite initial pending count.

A bounded physical oscillator can construct its own root envelope instead of assuming finite events. Let its retained remaining phase r decrease with actual rate a(t), where0<=a(t)<=v, and let each genuine strobe reset r to a period p>=p_min>0. Between the enumerated overwrites and strobes, r'= -a(t); no other phase jump is hidden. The initial remaining phase may be arbitrary in its admitted nonnegative range. On an interval I of length L with no independently caused phase overwrite, consecutive strobes consume at least p_min of integrated phase advance; hence (N(I)-1)*p_min<=integral_I a(t)dt<=v*L whenever N(I)>0. Apply the inequality to every finite prefix of strobes; its uniform finite upper bound excludes an infinite event sequence rather than presupposing finiteness. Therefore N(I)<=1+floor(v*L/p_min), including closed interval endpoints. If R(I) independently counted updates overwrite that phase, split the causally ordered strobe sequence at those updates, including distinct occurrences at the same numeric time, and sum: N(I)<=R(I)+1+floor(v*L/p_min). An update may thus earn one extra early strobe, not an uncounted fresh oscillator or arbitrary repeated reset. Each same-time overwrite/strobe pair still needs the finite causal-order/descendant assignment below. A reset loop with neither a new bounded root nor a positive phase period fails this construction.

The A-prime predecessor sampler consumes this law with a(t)=min(1,U(t)), v=1 and p_min=1. Its all-mode strobe envelope is1+floor(L) before physical takeover, even under variable/depleted U; this follows from the integrated phase law, not from extending the constant-U diagnostic integrator. At U=0 the phase can remain still while real time and other components continue. A strobe has a total paid or partial-work/held-output outcome and resets its phase to a positive period; it cannot create an urgent zero-time self-loop. Nominal delay<=101/100 additionally consumes actual funded U and the upper period bound. That service conclusion is separate from event finiteness. The oscillator derivation has independent bounded review at this retained-phase and causal-order interface. The particular gate-source clock/cost branches also have their own bounded independent checks; actual placement and complete source interconnection remain separate duties.

Every generated completion, timeout, rejection, contact consequence or bookkeeping transition either has a root ancestor with strictly decreasing descendant rank and branching at most b, depth at most r, or is charged to an independently bounded physical event. One root then has at most D_r=sum_(k=0..r)b^k descendants including itself. Zero-delay consequences are allowed because their total is finite. A self-rearming loop that consumes neither a new root nor decreasing rank fails the certificate.

For a latch ell, suppose repeat toggles require actual coordinate variation h_ell>0, speed is bounded by v_ell, and each independently counted reset can contribute at most a_ell additional toggles. A finite integer-rounding allowance c_ell gives

    N_ell([0,T]) <= c_ell + a_ell*R(T) + v_ell*T/h_ell.

Position jumps need their own root/variation debit. An alternative is monotonicity between driver updates: k thresholds give at most k crossings in each held interval. Event classes and their drivers must be assigned consistently; a trigger cannot cite itself as an independent root. Let A(T) be the finite bound on these physical seeds. Then

    N_all([0,T]) <= D_r*(P0 + R(T) + A(T)).

This is a finite bound; N_all<=K*(R+N_all) would not be one. Bounded speed alone is insufficient: (T-t)^3*sin(1/(T-t)) has bounded derivative and infinitely many zero crossings before T. A switching guard therefore needs actual hysteresis, latch, monotonicity or a separately charged root; merely naming a continuous variable does not prevent Zeno switching.

Every event has a nonempty actual transition relation retaining physical domains, storage, destinations and outstanding commitments. In addition, the local mode-boundary coverage certificate requires either permitted flow continuation through the stated domain until an actual event, or an enabled nonempty transition at every boundary where the source forces flow to stop. Totality of events that happen is insufficient if a finite guard boundary forbids continuation but enables no event; that deadlock would satisfy the count bound while defeating concatenation. Empty work, unavailable input and malformed code lead to actual wait/reject/partial outcomes. Same-time batches have a finite permitted causal order, with every admitted choice retained. Resetting a request cannot turn prepaid old work into a fresh unpaid obligation.

Between consecutive events apply the held-mode result to actual retained state. At each event apply a total source transition and continue. A finite maximal run cannot end at event accumulation because the inventory bounds it, or at state escape because the physical envelope/continuation hypotheses exclude it. It therefore extends. This proves time-divergent continuation for every admitted causal choice at this interface. It does not promise that a failed operation finishes, or select only successful endpoints. Useful deadlines still come from the separate phase/rank theorem.

No common runtime clock or roster-uniform minimum delay is needed here. Each fixed finite design has finite installed channels and bounds. Uniform locality, per-unit service and horizon as the roster grows remain RP2 obligations; finite-roster existence does not discharge them.

The [projected-work extension](PROJECTED-WORK-FLOW.md) allows a real stop velocity to enter winding and bank work even when the resulting drift is discontinuous as a pointwise function of position at the stop. It supplies the held-mode G3 proof for that case. [A′ on one physical source](A-PRIME-SOURCE-ASSEMBLY.md) connects this result to the frozen elementary port inventory and independently charged gate events. It gives all-mode continuation for the specified member with its explicit exterior WORLD converter and closed-face material trip. On the frozen throughput-only exterior the result instead covers an open neighborhood of the protected box; the initialized collar argument must keep the actual world there.

## Baseline suppliers, without its whole-run conclusion

The primary source retains q/phi, geometric strokes/cams, E/T/U/J_par, ready/pending one-shot work, field/tracker states, digital state, finite queue slots and physical destinations. Mechanical ports are explicitly reduced through

    phi' = B^T*C^-1*q - D^T*u - R*L^-1*phi,
    q' = j - B*L^-1*phi - G*C^-1*q.

The same actual B occurs in both equations. Positive bounded L/C, row/column bounds and admitted forcing give finite local coefficient bounds; retained q/phi are not replaced by transient currents/voltages. The mechanical W comparison supplies the hard envelope independently of successful renewal. Transit obeys T'=chi*2.05*d-4.1*T; operating energy receives actual4T and pays actual work. Clipped enable laws such as g(U) are locally Lipschitz. Physical pose end stops remain in D.

For thermal composition use Y=E_nonthermal+Ctheta*theta. Real internal refunds, spill and dissipation cancel from Y'. The store still has its own physical upper-stop relation, but its reaction is not copied into an unjustified off-diagonal normal-cone heat law. Recover theta=(Y-E_nonthermal)/Ctheta and prove its physical nonnegativity separately. The protected world box is never added as a normal cone.

A held inverse-L/C request has actual rate g(J_par)*r, freezing at a material endpoint. Work uses the realized motion. The source has44 such coordinates per host, each monotone under a held request and crossing at most one endpoint. Therefore at most44 bound-hit subdivisions per host occur per held interval. Within those modes the signed work law is locally Lipschitz; unfunded motion stalls. This finite-mode treatment avoids an unjustified product-reflection claim for coupled coefficient/resource reactions.

Actual root channels include the hard instruction-launch ceiling2^27, physical/parameter updates2^31, and separately priced/rate-bounded raw capture/receipt clocks. Their installed multiplicities and burst bounds must be retained. Initial pending requests and new instruction/capture/word operations have bounded one-shot descendants. Coefficient hits use the44-coordinate bound; cams/catches/release positions and E-on/off hysteresis require their actual travel/charge certificates. Samples occur through finite-rate operations: fluctuating analog values do not create digital events by fiat.

The world dynamics are regular on a neighborhood of the protected box. Local flow is obtained there before a safety conclusion. The initialized first-exit proof then keeps the world inside that region, while physical stock bounds permit continuation. This is a causal prefix use of the theorem, not an all-history safety/nonblocking premise.

The baseline's written mechanisms and `flow_existence_model.py --check` support these local suppliers at their existing scope. The remaining adapter work is an inspectable inventory assigning every actual event constructor to a root, bounded descendant or physical charge, and every continuous term to this coordinate map. That finite compatibility burden must be completed before claiming unchanged G3 reuse. A separate reviewer inspected the common composition argument and rechecked the repaired forced-boundary and input-indexed uniqueness conditions. That bounded abstract review does not supply the missing baseline inventories.
