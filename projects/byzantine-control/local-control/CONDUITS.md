# Actual contact currents, isolation and reconnection

Status: derived contact-network construction and explicit source-admission test. The current-divider calculation below repairs the open-current/reconnection error without treating demanded current as actual contact current. It is a conditional physical supplier, not admission of arbitrary rewiring in every component containing that network. Its exact remaining placement/fault obligations are stated at the end. The full program is not complete.

The consumer is unchanged: an intact decision must justify a consequential positive cut from its actual imperfect local evidence, and every conforming decision/realization chain must satisfy the fixed rule `ell <= 1` and `z >= .8` throughout the real pressure interval. The ordinary main image retains LOAD_MARGIN500 and ISOLATION_MARGIN180. These constants do not certify a physical network by themselves. The interface below covers all eleven named conduits and retains every direction, separately constrained contact and latent energy path; it does not collapse many unsafe contacts to a safe mean.

## Prior results and selected construction

[✓] [Gernandt et al., Port-Hamiltonian formulation of nonlinear electrical circuits](https://arxiv.org/html/2004.10821), sections2 and3, inspected for this construction: Kirchhoff interconnection preserves power, while resistive, capacitive and inductive component laws supply dissipation/storage separately. This is the conventional circuit foundation imported here; no new circuit theory is claimed.

[✓] [TI SNVAA45](https://www.ti.com/document-viewer/lit/html/snvaa45), Introduction and Improved Inductive Discharge Concept, inspected for this construction: opening a supply does not erase stored inductive energy; discharge topology, heat and simultaneous-channel ratings constrain the resulting time. Its particular converter is not imported as a Byzantine isolation device. [✓] [HSE Control systems](https://www.hse.gov.uk/comah/sragtech/techmeascontsyst.htm), Sensing and Wiring/communications, inspected for process-connection and common-utility dependence. Neither source supplies this program's spatial fault map.

The bounded search covered contact current during opening/reclosing, inductive discharge, resistive current division, and common-mode isolation. The closest results already provide circuit conservation and ordinary discharge methods. The remaining contribution is the exact source adapter: preserve actual connector quantities, subsequent physical changes, pending pressure, corrupted interior terminals and one resource history. No bounded search is evidence of novelty or absence of another suitable construction.

## A current-bearing contact with an actual open state

For one physical conductor lane, let `a in [0,60000]` be its actual cut travel and `s in [0,40000]` its actual shunt travel. Let `c=1-a/60000`, `b=s/40000` and `h=c(1-b)`. These are real conductance controls, not reported positions. Install two resistive branches from node `v`: conductance `I_* h/R` to the actual body terminal at potential `V_b`, and conductance `I_*(1-h)/R` to the local dump return. Inject actual current `I_* J` at that node, where `I_*>0`, `R>0`, and `J(t) in [19/10,2]`. `R` is a voltage scale; the physical resistance at unit conductance is `R/I_*`. An upstream stock must fund this source and its dump, as discussed below.

Kirchhoff's current law and Ohm's law give

    v = R J + h V_b,
    I_contact/I_* = h J - h(1-h)V_b/R,
    I_dump/I_* = (1-h)(J+hV_b/R).

At an actual open `c=0`, the contact branch has zero conductance and carries exactly zero current. At full shunting `b=1` it also carries zero. Reconnection increases `c` continuously and therefore increases the actual branch current continuously except for the bounded terminal/source residual below. No upstream-demand variable is substituted for that current. At `h=1`, actual contact current is `I_*J`, independently of the body voltage; the reachable loaded running state is therefore genuinely above the fixed unit cut threshold.

The finite-energy interpretation is explicit. With source power `P_src=I_*Jv`, body-port power `P_body=I_contact V_b`, and nonnegative resistor heat

    Q_branch=(I_*h/R)(v-V_b)^2,
    Q_dump=(I_*(1-h)/R)v^2,

the exact identity is `P_src = P_body + Q_branch + Q_dump`. A negative `P_body` is real body-to-network energy, not negative cost that may be omitted. This algebraic version has no inductive or capacitive store of its own; a storing implementation adds its actual state and cannot keep the same opening/reconnection equations without a refinement proof. Stored operating energy behind the body terminal remains in that body's account.

Assume the actual body terminal satisfies `|V_b| <= R/5`. Then `I_contact` is nonnegative, and its normalized actual load is

    ell = I_contact/I_* = 2h + e,
    e = h(J-2) - h(1-h)V_b/R in [-3/20,1/20].

The bound permits arbitrary repeated changes of `J` and `V_b` inside their ranges. It neither assumes them constant nor bounds their total variation. Since `h` is Lipschitz with `|h'| <= |c'|+|b'|`, actual cut/shunt speeds at most `11/10` imply

    ell(t)-ell(u) <= (11/120000)(t-u) + 1/5
                         <= (1/10000)(t-u) + 1/5.

This includes opening and reconnection. At a sample taken when the contact is open, a later large connected current requires actual travel; it cannot appear by replacing `c=0` with `c=1` at a discrete mode change. A contact model with such a jump is a different source and fails the demonstrated inequality.

The same calculation covers fixed passive failure coefficients. Replace `h` by any convex combination of `1`, `c`, `1-b` and `c(1-b)`, with nonnegative coefficients summing at most1. A stuck-open path, a permanent shunt bypass, a permanent cut bypass and combinations of them are included. The derivative bound remains the same because each partial derivative has magnitude at most1. A broken shunt can keep a closed contact near load2 even at its reported full-shunt position; direct functional sensing then refuses the cut. No return is promised for that persistently failed target. A new electrically switched bypass that changes these coefficients arbitrarily after sampling is not covered by the fixed-coefficient branch; its explicit counterexample is retained below.

## Bundles, both directions and the eleven-conduit catalogue

If one named conduit contains finitely many separately constrained lanes, define its actual load as the maximum of the lane loads, each divided by that lane's physical safe-current rating. Both directions are retained. Every lane needs the displayed source/terminal/travel bounds or a separate stronger bound. The maximum preserves the same one-sided future envelope: choose a lane attaining the later maximum and compare it with its own earlier value, which is no greater than the earlier maximum. A mean does not have this preservation property.

The source cut catalogue is therefore an index of actual constrained bundles, not an assertion that each bundle contains one wire. The following is the required complete lane map; a row is not discharged by writing its name here.

| Conduit | Actual quantity and required lane coverage |
|---|---|
| SUPPLY_IN | Every operating-energy feed crossing the bank cut, including charger/recharge and normal source-cache/CPU replenishment; current on the body branch of the actual divider, not its upstream injected current |
| SUPPLY_RETURN | Every return/backfeed conductor of those same loops; a paired two-terminal loop is charged once as an energy source, while both constrained poles satisfy their actual current ratings |
| MAINTENANCE_FEED | All ordinary maintenance generator and write-driving feeds, including simultaneous held channels and aliases after their fixed-array combination |
| MAINTENANCE_RETURN | All reverse mechanical/electrical return and residual-charge paths of that distribution; a body-to-network energy flow remains in the conservation identity |
| WORLD_1 | Every energetic lane of the first actual world interface, including all allowed internal redistribution into it; four named nominal trackers alone do not bound the faulty export |
| WORLD_2 | The corresponding second-coordinate interface, with its independent current and possible reverse flow |
| DATA_TX | All ordinary report, command, write and raw-fragment egress, including staging already past an upstream cut |
| DATA_RX | Ordinary primary-frame/request ingress and its backfeed; independent auxiliary raw-record paths remain separately mapped and cannot be hidden in this row |
| RUNTIME_WRITE | Every admitted DMA/debug/capture writer and its energetic path; an unlisted route to running C is still a source failure |
| ACTIVE_SENSE | Probe energy, selector/calibration and return paths; a read-only semantic role does not imply zero current |
| SERVICE | Every admitted privilege/service ingress and its retained capabilities, pending work and backfeed |

Fast lanes may instead have a genuine whole-history bound `ell <= 1/5`, including all body stores, incoming energy and mode changes. Such a lane satisfies the one-sided envelope with zero slew and jump1/5. This is a physical rating result, not a unit change or a claim based on nominal packet amplitude. Its rating must be established from the complete hard export map. The high-load supply/diversion branch remains nontrivial even when low-energy signalling lanes use this stronger bound. No adoption of larger safe-current ratings is licensed without including the resulting connector/mechanical/source properties.

## Functional isolation as a separate network property

The load result does not prove isolation. A concrete passive isolation family can expose a normalized total leakage conductance

    g = d + k(1-y) + p,
    z = max(0,1-g),

where `y` is actual normalized sleeve/isolator travel, `|y'| <= 11/400000`, fixed unknown `d,k >= 0` satisfy `d+k <= 1`, and arbitrary parasitic conductance `p(t) in [0,1/10]` is retained. The three summands are parallel nonnegative passive conductances; `g` may reach1.1. The lower clipping in `z` is the definition of the normalized isolation rating, not a circuit that suppresses excess conductance. The property measured is the actual total functional transfer, not the sleeve's reported position. The two-time inequality is

    z(u)-z(t) <= (11/400000)(t-u) + 1/10.

Clipping is1-Lipschitz and monotone, so the bound holds even when individual parameters are unknown, the isolation mechanism is jammed, or the permanent bypass `d` makes the full stop unsafe. For nominal return, use the narrower actual range `d=0`, `k in [.995,1]`, and `p in [0,.005]`; then a full actual stroke gives `z>=.995`, stronger than GEOMETRY's required `.99`. The broader failed family can be refused indefinitely at its charged persistent footprint. It is not falsely promised useful return.

This is a constitutive realization only when every leakage path crosses that actual network. The current all-fixture arbitrary-rewiring wording does not prove this. An interior rewire may change terminal potentials without changing the external conductances, but an event that inserts or switches a bypass around the network changes `d` and needs its true additional variation. In particular, a full isolation short immediately after a truthful sample can violate the next intact decision and the pending pressure interval. It cannot be excused by marking the target P. The same-history physical placement must determine which of these two events is possible, before the outcome is judged.

## Matching the actual stored guard

The checked main geometry record supplies the complete functional horizon

    A = 133004488461/67108864,

including acquisition/folding, execution, repeated withdrawal, transport and physical tails. It is larger than the raw functional sample age; substituting the age alone would be unsound. With sensor error1/100, the two consumed margins are

    1/100 + A/10000 + 1/5 < 1/2,
    1/100 + 11A/400000 + 1/10 < 9/50.

For a source-valid member report passing the ordinary load threshold `.5`, the actual load remains below1 through its complete consumed horizon. For the isolation-deficit report passing `.02`, actual isolation remains above.8. Different members may have different sample times; each receives its own full horizon before the max-fold argument is applied. The one-sided load-threshold adapter in PROBE-MAP remains necessary at saturation; a clipped overload is not a precise two-sided sample.

At a nominal full shunt every divider lane carries zero current, while at a nominal full isolation stop `z>=.995`; even worst nominal error leaves the existing permission guard available once the actual acquisition has refreshed. At a closed unshunted powered loop, `ell>=1.9`; the same physically available cut is prohibited and the unchanged guard refuses it. Failed isolation/shunt/cut networks can also be physically probed and refused. This is a consequential recovery constraint, not a calendar or an unrelated control action.

## Energy, voltage and a noncircular candidate point

The voltage hypothesis cannot use one global bound containing the upstream node: `R>=5V_global` and `v≈2R<=V_global` are inconsistent. Enlarging every stock together does not repair that algebra. Keep the body and feed domains distinct in the actual graph. A preliminary compatible raw point has body hard stock `C_B=2^64`, minimum body-terminal capacitance `2^-32`, hence `|V_b|<=2^49`; a separate feed stock `C_F=2^96` can support its higher-potential nodes. Choose `R=2^52`, `I_*=2^15`. Then `R>=5*2^49`, source node voltage is below `2^54`, and source power per independently powered loop is at most `(22/5)I_*R < 2^70`. This is a candidate finite electrical point, not an established new resource certificate.

That point consumes two substantive graph facts: all body-terminal charge remains within the body hard-energy/capacitance law even under admitted internal rewiring, and the high-potential feed node cannot be directly substituted for a body terminal by an admitted ordinary or physical bypass. If those facts fail, use the larger actual terminal bound and redesign the circuit; do not keep the convenient smaller voltage in the equations. No source-current regulation, divider, passive isolation path, delivery lower bound or capacitor minimum is certified by this numeric substitution. In particular, an arbitrary defect reaching both the feed current source and its divider defeats `J in [1.9,2]`. A separate surviving endpoint or a different bounded-current storage architecture is then required.

Nominal operating power and charging must be checked at the actual carrier voltage. Current alone does not give a constant charging-power lower bound from an empty capacitor. The source may use the existing physical voltage/energy launch threshold, but must derive pre-threshold charging, capsule demand and subsequent sustained output from the new circuit. Every dump loss, concurrent lane, return input and larger upstream reserve belongs in the common bill. The existing Eon/Eoff/H record is not automatically valid after adopting this network.

## Countercases and exact remaining admission obligation

The executable retains five distinct false passes. A zero open-contact sample followed by an instantaneous loaded reconnection violates a claimed zero-slew law. A fixed-damage proof reused for a newly switched shunt bypass violates its future-load bound. A freshly switched full isolation short defeats the isolation margin despite truthful samples. A global voltage bound used to scale its own larger source is inconsistent. A source-side resistor proof whose supposedly bounded current source is bypassed can exceed its entire margin. These are explicit changes to the stated source, not discovered failures of the proved algebra; their admission status is precisely the unresolved physical map.

The surviving contribution is an actual current/conservation/reconnection theorem, an all-lane preservation law, a separately characterized functional-isolation family, and their exact transport into the current stored guard. It answers the mathematical question that the former demanded-current shorthand left open. To admit it in W0, the coordinator must bind actual lane topology and fault reach, source-current/terminal voltage suppliers, isolation bypass reach, all stores/thermal paths and nominal power delivery in one source. An independently fallible external boundary may supply these with its real fault projection; relabeling it as permanently healthy cannot. The alternative inductive approach remains live: a surviving series current state with bounded terminal voltage yields physical slew, but its open-arc/freewheel topology, reconnection state, stored energy and longer unloading delay need their own construction. Neither pending approach is full-source completion.

## Reproduction and verification boundary

Run `C:\Python312\python.exe -B conduit_model.py --write` to produce a reviewed record and then `--check` for independent regeneration. The executable uses exact rational arithmetic for Kirchhoff/power identities, unknown/passively damaged coefficients, two-time residual bounds, opening/reconnection, bundles, guard margins and explicit countercases. It binds CONDUITS, its own source and the current geometry/port/probe inputs. The written inequalities establish the continuous parameter claims; finite rational enumeration is independent algebra/encoding evidence, not a proof by sampling of every physical device. Independent source review is still required before adoption.
