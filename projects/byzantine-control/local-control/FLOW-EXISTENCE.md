# Continuous continuation without a fictitious safety projection

Status: derived continuous-mode construction, independently checked at its stated scope; the complete source-mode map remains open. It extends the continuous supplier consumed by [HYBRID](HYBRID.md), rather than assuming that separate scalar circuit solutions automatically assemble. It does not yet certify the complete electrical/control network. The existing finite-event and hysteresis arguments remain separate consumers.

## Prior result and remaining obligation

[Camlibel and Schumacher, Linear passive systems and maximal monotone mappings](https://link.springer.com/article/10.1007/s10107-015-0945-7), Theorem3, was inspected independently on2026-11-05. It gives a unique locally absolutely continuous state solution for a passive linear time-invariant backbone with positive-definite quadratic storage, a static maximal-monotone relation, its stated range qualification and compatible initial state, under locally integrable forcing. Variable inductance, changing topology and a linear finite work cell are not automatically in its hypotheses. State uniqueness does not automatically give uniqueness of eliminated algebraic port variables.

The construction below exposes charge/flux coordinates and the elementary resolvents needed by this diode/brake/stop class. It reconstructs standard monotone evolution reasoning for this adapter; no novelty is claimed. Kirchhoff power conservation alone is insufficient. Every actual mode must first yield consistent coordinates, initial data and inputs. Parallel contradictory ideal voltage sources demonstrate why individually functioning components need not have a functioning interconnection.

## Covered continuous mode

Use finitely many real state coordinates y. A selected set J consists of retained flux coordinates, without artificial clipping. Some other coordinates have physical unilateral diode or end-stop constraints forming a fixed product of closed intervals D; the remaining coordinates are unconstrained. The protected world coordinates are unconstrained in D. The world safety region K is never inserted as a normal-cone constraint: its invariance must follow from actual control and dynamics.

After eliminating only genuinely consistent static relations, a mode has

    y_dot + n + sum_(j in J) b_j(t,y)*xi_j*e_j = f(t,y),
    n in N_D(y),    xi_j in Sign(y_j),    y(0) in D.

N_D is the outward normal cone of the actual physical stops/diodes, Sign(0)=[-1,1], and the flux coordinates j are unrestricted in D. The coefficients are measurable in t, locally uniformly Lipschitz in y and bounded on compact time/state cylinders; b_j is nonnegative. Global continuation uses linear growth of f and bounded b_j on each finite horizon, or an independently proved compact physical invariant with an extension of the local functions outside it. No desired safety predicate may define a missing flow outcome.

These hypotheses permit a brake coefficient to depend on actual rail voltage or mechanical position. Positive bounded C and L permit voltage/current reconstruction from charge/flux; their inverses enter f. A time-varying L in a supplied measurable interval therefore differs from a disappearing inductive state. Its mechanical work and locally finite constant-flux jumps still require CURRENT-CUT's separate energy law. Hidden storage and inconsistent ideal constraints must be supplied before claiming this coordinate reduction.

## Construction and uniqueness

On a cell of length h, average the actual coefficients over the cell with state argument fixed at y_k. Put v=y_k+h*average(f(t,y_k)). For each flux coordinate use

    y_(k+1),j = sign(v_j)*max(|v_j|-h*average(b_j(t,y_k)), 0).

For each physical interval coordinate project v_j onto its interval; leave unconstrained coordinates unchanged. These scalar resolvents exist for every v. Flux zero admits precisely the passive brake reaction interval; a clipped physical stop has its normal-cone reaction. No world-safety projection occurs.

Since y_k lies in D and projection is nonexpansive, its displacement is bounded by h times the forcing bound; the distance to D also bounds the normal reaction by that forcing bound. Soft thresholding changes its argument by at most h times the brake bound. Thus polygonal interpolants have uniform derivative bounds on bounded time/state cylinders. Linear growth and discrete Gronwall give a finite-horizon bound; alternatively the independently proved physical invariant supplies it. Finite-dimensional compactness yields a uniformly convergent subsequence with weakly convergent bounded derivatives and weak-* bounded Sign selectors. Interval averages, rather than endpoint samples of arbitrary measurable inputs, converge in the integrated equations. Uniform state Lipschitz bounds permit replacing y_k by the limiting state; the resulting averaged brake coefficients converge strongly in L1, which justifies their products with the weak-* selectors. The scalar Sign and normal-cone graphs identify the limiting reactions through their integrated monotonicity inequalities. This gives an absolutely continuous solution of the displayed equation.

For uniqueness, normal-cone monotonicity gives (n_y-n_z) dot (y-z)>=0. Split each brake term as

    [b_j(t,y)*xi_y-b_j(t,z)*xi_z]*(y_j-z_j)
      = b_j(t,y)*(xi_y-xi_z)*(y_j-z_j)
        + [b_j(t,y)-b_j(t,z)]*xi_z*(y_j-z_j).

The first term is nonnegative; the second is at least -L_j*||y-z||^2 because |xi_z|<=1. The forcing contributes at most L_f*||y-z||^2. Hence

    (1/2)*d||y-z||^2/dt <= (L_f+sum_j L_j)*||y-z||^2.

Gronwall with equal initial states gives the same state path. It need not give a unique individual diode reaction or algebraic current when several internal reactions realize that path. Every source-consumed port variable needs uniqueness or its full allowed relation retained in the semantics. Finite-horizon continuation bounds and uniqueness permit gluing to an indefinite path. Local Lipschitz regularity without a continuation bound earns only local existence.

## The actual source map still matters

The reduction retains all stored charge/flux and real return paths. Clipped resistors, threshold shunts, valid fixed linear ratios and bounded command-driven laws give Lipschitz terms after a consistent reduction. Positive capacitances/inductances supply dynamic coordinates. Passive Sign brakes and physical stops give the reactions above. A transformer network needs its actual independent-coordinate reduction; inconvenient algebraic constraints cannot be deleted. Hard material and thermal bounds supply continuation estimates only after complete stocks and inputs are counted.

The finite900V work cell is not a positive quadratic capacitor by a change of name. Its state, charger, one-shot connection and endpoints need their own relation and transitions. The actual instruction debit proves that a connected funded operation stays away from empty storage even for an arbitrary admitted opcode. That covers its active mode. Disconnected, charging and empty modes and their boundaries remain explicit source consumers.

Supplied measurable forcing also differs from arbitrary instantaneous state-feedback. Against a causal adversary, the source must show either that its realized feedback has the above regularity or that actual propagation/hold/update structure determines inputs successively on positive intervals. HYBRID supplies the latter construction for its digital interfaces. A peak bound on an extra active element does not supply it. For example x_dot=1 when x<=0 and x_dot=-1 when x>0 has no ordinary absolutely continuous solution from0. Its Filippov completion would be a different physical relation, not a free repair of run nonemptiness.

After continuous-mode suppliers are matched, HYBRID's finite launches, bounded one-shot completions, idempotent catches and positive travel/hysteresis gaps give locally finite event batches. Coefficient/damage jumps must preserve domains and retain their charged energy/state transition. Rejection and power loss retain flow outcomes. Concatenating these actual modes and transitions supplies nonempty hybrid runs. Safety, service and return still require INITIAL-RETURN's separate induction.

## Verification boundary

`flow_existence_model.py --check` verifies rational resolvent inclusions, monotonicity probes and the state-dependent brake estimate on an explicit coupled class. It retains incompatible ideal sources and world-state projection as rejected substitutes. The universal proof is the argument above; finite checks do not mechanize compactness or passage to the limit.

Independent review reopened Theorem3, reproduced the checker and checked the bounded reactions, strong-L1 coefficient/weak-selector limit and state-dependent uniqueness argument. The complete mode/port/initialization map remains mandatory. In particular, the combined prospective-isolation and retained-current apparatus must enter the same charge/flux model. Until then, this is a conditional continuous supplier, not W0 admission or program completion.
