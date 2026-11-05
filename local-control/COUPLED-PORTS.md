# Coupled physical storage, clearance and delivery

Status: derived generic module and assembly criterion; independently re-derived and executable checks reproduced at c70a9e3, with the canonical extraction checked for exact certificate equality and the clarified8896103 record reproduced in the integration worktree. Full-program source selection and instantiation remain open; this checking status is not repository acceptance. The optional detailed CURRENT-CUT asset remains in the evolution research branch, including its incomplete terminal inventory and exact-zero reduction issues; none is imported as a premise here. This module provides one stateful primitive with explicit ports. It is neither a successful-intervention opcode nor a manufactured-device claim.

[✓] Sontag, [Input to State Stability: Basic Concepts and Results](https://www.sontaglab.org/FTPDIR/04cetraro_reprint.pdf), sections2.3-2.4, supplies the prior framework: bounded-input state estimates retain initial states and transient response. The result below is an explicit weighted comparison for this source, rather than a novelty claim about input-to-state stability. The previously inspected port-Hamiltonian conservation laws supply the effort/flow account. The comparison is proved directly, including coefficient uncertainty; it is not obtained by calling an arbitrary interconnection passive.

### State, ports and fault polarity

Each represented channel retains a generalized momentum phi_e and each apparatus-side storage node retains q_n. In the electrical interpretation these are magnetic flux and capacitor charge; in the mechanical interpretation below they are momentum and deformation. Positive storage coefficients satisfy 0<L_e,min<=L_e<=L_e,max and 0<C_n,min<=C_n<=C_n,max. Flows are i_e=phi_e/L_e and node efforts are v_n=q_n/C_n. B is the actual signed storage-node/channel incidence; D is the actual channel-to-body/tool boundary incidence. Both are physical maps, not requester-supplied addresses. Every possible enabled route stays represented, including a disabled route's retained state. A physical reconfiguration may change a finite declared incidence mode, but must retain the actual state and satisfy the same common certificate; it cannot merge inconsistent stored states through an ideal reset.

The module equations are

    phi' = B^T v - D^T u - R i,
    q'   = j - B i - G v.

Here j is the complete incoming current at the receiving capacitor nodes, u is the effort at the actual body/tool boundary, and G is the physical dissipative shunt. Additional passive shunts or freewheel relations may be included only with their actual sign and state constraints. The outward boundary flow is y=D i. Thus the two electrical power ports are v^T j and -u^T y. The material state stores

    E = sum_e phi_e^2/(2L_e) + sum_n q_n^2/(2C_n).

For differentiable coefficients,

    E' = v^T j - u^T y - sum_e R_e*i_e^2 - sum_n G_n*v_n^2
         - .5 sum_e i_e^2*L_e' - .5 sum_n v_n^2*C_n'.

E (equivalently H in the source composition) is physical stored energy, measured in work units. W below is a clearance potential, not a spendable reserve: in electrical units phi has volt-time units, q has charge units, w is dimensionless and a has resistance units; therefore W has volt-time units and F has voltage units. In the mechanical interpretation a has damping-coefficient units, W has momentum units and F has force units. Source affordability is derived from E and the actual effort-flow balance. No proof may debit W to fund an instruction or a mechanical intervention.

Those unit assignments concern each homogeneous interpretation. A mixed-domain connection must provide its actual effort/flow conversion and weights into a common comparison unit; it cannot add electrical flux and mechanical momentum by assigning both the same field name. The numerical inequalities apply after that declared normalization. Physical work remains one common energy unit and the conversion must preserve its port balance.

Internal incidence power cancels exactly. Coefficient changes retain their actual mechanical work and jump-energy transfers; they are not a free disturbance. The current estimate below uses retained phi,q and bounded coefficient values, so it does not need to differentiate L or C. Physical energy histories still need the declared paid-work regularity. A capacitor at a body/tool terminal is either inside that recipient's retained state or an explicit boundary charge port; it is never silently counted as apparatus-side storage.

There is an exact mechanical port interpretation of these equations: q is deformation, phi is momentum, C is compliance, L is mass, v=q/C is spring force and i=phi/L is velocity. Driver velocity j, dissipative creep Gv, mass damping Ri and external load u give q'=j-Bi-Gv and phi'=B^T v-D^T u-Ri; stored energy is elastic plus kinetic and the port powers remain v^Tj-u^Ty. This is an exhibited effort/flow correspondence for the declared finite primitive, not a claim that every electrical micro-realization implements that mechanism. A changing-mass/compliance implementation must account for actual momentum and parameter-work ports. Mechanical safety may consume both force and velocity bounds: zero momentum with nonzero deformation still stores stress. The actual contact decoder must retain all forces, movements and stored effects that its fixed admissibility rule distinguishes; correspondence alone does not make a hidden damper or shared return irrelevant.

The useful-clearance premises concern the actual obtained brake configuration: R_e>=r_e>0, G_n>=g_n>0, |(D^T u)_e|<=U_e, and |j_n|<=J_n. A command, truthful status bit, or ended intrusion does not establish these inequalities. Their suppliers are the same contested actuation, receiving-boundary and replenishment histories used by the larger source. A physically failed brake may violate them; its intact issuers still owe the separate universal current guard. The map from that physical failure to unavailable renewal targets and independent outward effects remains fixed before outcomes.

### One compositional inequality

Choose positive weights w_e,a_n and rate k>0 satisfying, for every channel and receiving node,

    w_e*r_e/L_e,max - sum_n a_n*|B_ne|/L_e,min >= k*w_e,
    a_n*g_n/C_n,max - sum_e w_e*|B_ne|/C_n,min >= k*a_n.

These are the common compatibility conditions, not independently chosen local success claims. Set

    W = sum_e w_e*|phi_e| + sum_n a_n*|q_n|,
    F = sum_e w_e*U_e + sum_n a_n*J_n.

Taking upper right derivatives of absolute values and applying the two inequalities gives

    D+W <= F - k W,
    W(t) <= exp(-k(t-s))*W(s) + (F/k)*(1-exp(-k(t-s))).

This bound is uniform in unknown time-varying L,C within their intervals. The fixed physical output satisfies

    |y_p| <= sum_e |D_pe|*|phi_e|/L_e,min.

The same sublevel separately bounds effort and flow: |v_n|<=W/(a_n*C_n,min) and |i_e|<=W/(w_e*L_e,min). It also has a typed relation to physical energy. By Cauchy-Schwarz, W^2<=2E*(sum_e w_e^2*L_e,max+sum_n a_n^2*C_n,max), so an initial W bound can be derived from the very same physical stock. Conversely E<=.5*W^2*max({1/(w_e^2*L_e,min)} union {1/(a_n^2*C_n,min)}). These are comparison inequalities, not an identification of E and W. They keep residual energy and the actual force/current requirements distinct.

Consequently every current and remaining output-power claim is decoded from the same W and the same boundary incidence. Shared nodes, signed cancellation and circulating current are not erased: B controls internal exchange, whereas the absolute channel terms retain energy and every D-visible continuation. This is the reason to use an incidence-based certificate instead of one scalar lemma for each named wire.

For one node and one neck channel, take any 0<a<=r/(2*rho_L), where rho_L=L_max/L_min, set k=r/(2*rho_L*L_min), and choose

    g >= (C_max/a)*(1/C_min + k*a).

The resulting source has W=|phi|+a|q| and F=U+aJ. A smaller a reduces the contribution of continuing source current J, at the price of a larger real shunt g. This exposes the actual design tradeoff. No exact stopping claim is required: the elementary capacitor/diode counterexample L=C=1,R=2,B=1,u=.5 has i(t)=.5*t*exp(-t)>0 at every finite t. A source may instead prove a genuinely nonstoring Sign primitive, but adding a parallel capacitor is not that proof.


### Clearance, bank retirement and continued service consume that inequality

Choose one physical clearance level W_*>0 with F/k<=W_*/2. If W(s)<=W_0, let n be the least nonnegative integer with 2^n>=2W_0/W_*. Then T_clear=n/k suffices for W(s+T_clear)<=W_*: exp(-1)<1/2 provides the elementary bound. The sublevel remains invariant while the actual brake and input bounds remain held. No source state is assigned zero at T_clear. In particular, latent capacitor charge and freewheeling flux remain available to every later proof.

For each physical pressure contact p, the required decoder is the actual incidence bound above, including the union of physically possible continuations if D changes during the pressure lifetime. Its normalized clearance current must fit the factual load/isolation threshold with the same measurement-error and future-age allowance used by ordinary P. For the separate two-reference-capacitor Z construction, its KCL exposure multiplier is an additional explicit decoder; it is not silently absorbed by renaming i. Runtime observation still uses the actual ordinary raw heads. W is an analysis certificate, not a new permission estimator or a truthful aggregate supplied to the program.

Let epsilon_p be the resulting bound on each actual body-input current after clearance. Then the remaining old-bank input power is at most sum_p U_body,p*epsilon_p, plus its already counted other inputs. The retirement consumer is the single inequality

    P_other + sum_p U_body,p*epsilon_p + k_body*B_ref < k_body*E_off.

Together with the actual carrier/shunt/return law, this makes the total launch-capable stock decay below its real launch threshold in a finite additional dwell. It does not assume that an old CPU halts on command, that a capacitor was erased, or that the brake can be released before real retirement/reconstruction. A bypass from q to the bank outside D defeats this decoder. The same bridge must also preserve the keeper's useful power and the actual writer/activation exclusion; those are consumers of the common source history, not promises made by this one electrical module.

Useful recovery consumes the same q,phi in a distinct obtained delivery configuration. One sufficient one-channel condition has a real unidirectional, current-limited charger

    j = clip(G_ch*(V_up-v),0,J_max),

with upstream voltage V_up>=V_up,min derived from actual usable reserve. It has actual input work V_up*j, delivered work v*j and nonnegative resistor loss (V_up-v)*j. The charger does not set q to a desired value. A real overflow shunt supplies an upper charge barrier; it is not an energy clipping operation.

For example, fix retained bounds |phi|<=Phi_max and |q|<=Q_max, desired current i_ready>0, q_ready=C_max*v_ready, and phi_ready=L_max*i_ready. Choose a delivery region whose spill-free lower face q=q_ready satisfies

    j_min > g_on,max*(q_ready/C_min) + Phi_max/L_min + eta,
    v_ready > U_body + R_on,max*rho_L*i_ready + delta,

for eta,delta>0. Here j_min is derived from the actual charger at every v<=q_ready/C_min; in particular V_up,min must exceed that voltage. The source and overflow upper barriers must simultaneously preserve the retained Phi_max,Q_max bounds. While q<=q_ready the first inequality gives q'>=eta even for an initially negative charge and adverse retained strand current, so q reaches that face within (Q_max+q_ready)/eta. Once that face is invariant, phi reaches phi_ready within (Phi_max+phi_ready)/delta. At phi_ready its derivative remains positive, and L<=L_max yields actual current at least i_ready. These are sufficient conditions with explicit physical headroom, not a claim of maximal permissiveness.

A sufficient retained upper rectangle is explicit. Write v_max=Q_max/C_min and require Phi_max>=L_max*(v_max+U_body)/R_on,min. Use a symmetric passive overflow h(v)=G_over*sign(v)*max(0,|v|-v_spill), with Q_max/C_max>v_spill and G_over*(Q_max/C_max-v_spill)>J_max+Phi_max/L_min. Both q faces and both phi faces are then inward. This uses real dissipation and permits negative initial charge; it does not project q onto the desired operating region. The spill-free lower-face ordering below makes the same overflow compatible with the delivery argument.

A variable-capacitance interval also constrains the actual lower/upper charge geometry. A lower target q_ready=C_max*v_ready is not compatible with an arbitrarily narrow voltage band when C_max>C_min. For an overflow beginning at v_spill, sufficient ordering is q_ready/C_min<=v_spill and q_upper/C_max>v_spill. The charger, shunt and input peak must give an inward upper q face. This condition retains coefficient uncertainty instead of restarting a narrow-voltage proof at each parameter value.

The bank's undervoltage consumer then uses i_ready>I_uv and its actual carrier capacitance to reach the launch voltage in finite time. At operating voltage, i_ready*V_body,min must exceed the complete work rate plus the required reserve margin. Normal charging, ordinary service and the later high-g brake share the same capacitors, fluxes, source connections and costs. Their mode transition uses finite conductance and retained state. The proof must not concatenate the low-current endpoint of one trajectory with an unrelated already charged delivery trajectory.

### One feasibility system and continuation obligation

The source-level certificate consists of a single compatible assignment of physical state bounds, incidence modes, weights w,a, actual R/G/charger parameters, input envelopes, current thresholds, reserves and time allowances. Its conditions are jointly: the two common W inequalities in every claimed brake mode; the pressure-current and residual-bank-power decoders; delivery lower and upper barriers; actual source energy/power balance; and the physical time and fault-history suppliers that obtain and maintain those modes. Their dependency on one another is part of the assignment. A result obtained by enlarging a reserve without paying its capacitance, or by enlarging a voltage without revisiting the current-growth bound, is not such an assignment.

The upstream state must pay sum(V_up*j), all other operating loads and losses on the same trace. Its usable reserve is established by the actual storage/delivery/dissipation system and admitted replenishment history, with usable storage distinguished from an energy upper bound. The optional CURRENT-CUT reserve calculation is one conditional electrical candidate, not a required implementation of this port law. In a charger interconnection, E_upstream' contains -V_up*j while E' contains +v*j; their sum contains the real resistor loss -(V_up-v)*j. A joint reserve therefore pays that one actual transfer and its losses, rather than choosing an unrelated budget for each proof. Internal work v*j is not a second independent resource. The common stored-energy account includes every q and phi, the upstream reserve, the body carriers and any actual reference network. Its initial winning region, hard material capacity and normally usable stock remain different data. A finite-health variant additionally consumes real wear state and replenishment; the invariant does not turn a wearing component into an inexhaustible one.

For the displayed fixed-incidence module, bounded measurable coefficient/input histories with strictly positive L,C and finite R,G produce a linear Caratheodory system in the retained coordinates phi,q. It has unique finite continuations on bounded time intervals. Locally Lipschitz clipped charger/shunt laws preserve this property; passive diode relations require their actual invariant state domain and monotone selection, as in the existing FLOW/HYBRID work. Charge/flux-preserving mode changes inherit the common W bound. The larger hybrid source must separately preserve consistent states, the same-history input bounds and its existing non-Zeno scheduling law. This module does not infer whole-source nonblocking from separate scalar examples.

The relevant kernel is explicit: this is a finite stateful port model with diagonal positive storage and the declared physical incidence/fault modes. Unlisted magnetic coupling, a new after-neck charge port, active negative damping not charged as an input, loss of the retained capacitance/inductance geometry, an unavailable mode falsely treated as obtained, or an inconsistent charged-node merge reopens its corresponding preservation law. The source may be a primary mathematical theory model; an optional finer electrical realization must refine these states, ports, trajectories, faults and resource consumers, rather than being required to mimic every informal circuit detail in the older asset.


The executable checks the incidence cancellation, W derivative and output decoder in11664 exact rational cases with shared nodes and an internal edge; these are encoding checks for the written general proof. It also checks a nonempty joint one-channel assignment on the same rectangle |phi|<=50, |q|<=32, L in[1,1.5], C in[1,2]. A finite current-limited charger with G_ch=1, delivery shunt G_on=0, real symmetric overflow and actual delivery resistance establish current at least1 within145 time units. The obtained brake R=1200, G=2048, with continuing incoming current bounded by64 and boundary effort by1, reaches actual current at most.01 within7/200 time units and maintains it; its residual boundary power is at most.01. Its spring-force bound is1.28, not.01: at weight a=1/128, W<=.01 permits |q/C|<=.01/(a*C_min). A force-sensitive contact rule must therefore choose its own clearance level, weights and output decoder. All states survive the mode change. This assignment demonstrates feasibility of the common inequalities and their distinct safety/service consumers. It is not the d40/B80 program source point, a manufactured apparatus, or a substitute for the full shared-source/fault-history instantiation. The old detailed electrical point remains a conditional refinement asset while that instantiation is selected. The authoritative full-program element inventory, modes, fault projection and mission interface must come from PORT-SOURCE; this generic assignment cannot replace them.
