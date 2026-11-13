# Discovering autonomous task components from partial readouts of a nonlinear ring

## Plain-language abstract

We observe only two parity signals from a recurrent six-bit system, not its six internal bits or its active interaction gates. The same five observations admit 22 hidden model-and-state explanations. We ask for a three-coordinate autonomous component that retains the first observed signal, without specifying its third coordinate. Local constraint solving discovers two possible components. Each has seven concrete witnesses, but no one model supports both choices. Thus the calculation both discovers boundaries and refuses to combine individually plausible discoveries that use different underlying systems. The discovered components have nonlinear, nonconstant dynamics, and their certificates hold for every initial state and every later step of their candidate model. Finite observations do not certify that this candidate is the actual environment. A second calculation exposes an interface obstruction even when both parent decompositions use the same model.

## 1. General family and declared unknowns

Fix n >= 5 and a finite observation horizon H. Coordinates x_j(t) are bits, indexed cyclically modulo n. There are unknown persistent mode bits theta_j. The universe of dynamics is

    x_j(t+1) = x_j(t) XOR (theta_j AND x_(j-1)(t) AND x_(j+1)(t)).

The modes and initial state are unknown. Modes are chosen once, not separately at each time or for each partial view. All 2^n initial states are admitted by each candidate model. A mode zero removes both incoming neighbor effects at that update; mode one gives a nonlinear two-neighbor interaction.

Available readouts are declared parity functions of small coordinate sets. The experiment provides only their values. It provides neither the hidden coordinate states, the modes, an autonomous partition, nor the identity of a third task-core coordinate. The family does assume a known finite latent coordinate vocabulary and a known nearest-neighbor gate grammar. That is a significant structural universe, but it does not identify the enabled gates or the desired component. There is no reset or membership-revealing operation.

The finite-state model is a candidate universe, not a statistical model-selection guarantee. This example is exact possibility discovery within that universe.

## 2. Primitive factors constructed directly from the update rule

Introduce variables theta_j and x_j(t), and readout factors for each observed parity. A transition factor has scope

    (theta_j, x_(j-1)(t), x_j(t), x_(j+1)(t), x_j(t+1))

and exactly 16 allowed rows, one for each assignment to its first four bits. The last bit is computed by the displayed recurrence. Thus the local relations do not consult an oracle deciding whether a whole candidate system exists. There are nH transition factors, each arity five. A two-bit parity observation contributes a two-variable factor with two allowed rows. The SAME theta_j variable is incident on every temporal occurrence of its transition rule.

A candidate task core S owns a subset of the coordinates and uses their full tuple as its internal state. It preserves a designated task parity if that parity's coordinates are in S. No exterior input is permitted for an autonomous core.

**Local autonomy criterion.** Projection onto S is an autonomous exact subsystem for all states iff, for every j in S with theta_j=1, both neighbors of j also belong to S.

Sufficiency follows by evaluating each retained update using coordinates in S. For necessity, if an active retained update has an exterior neighbor, set its other neighbor to one and vary only that exterior bit. The same retained state then has two different next retained states. This is a two-state certificate against autonomous realization. The full initial product assumption makes these states admissible. No observed-data coverage assumption is used to infer the universal identity.

Consequently autonomy contributes local constraints on ownership and mode variables. For a general core indicator c_j in {0,1}, the condition is

    c_j=1 and theta_j=1 implies c_(j-1)=c_(j+1)=1.

This is a four-variable Boolean factor. A required cardinality can be compiled with prefix-count variables, rather than an unrestricted whole-state relation. Task coordinates are forced to have c_j=1. In the six-bit calculation below, the size-three condition is represented more simply by one variable p selecting the third coordinate.

Taking the natural join of transition, observation, ownership and autonomy factors discovers a model, hidden trace and component together. Eliminating hidden trace coordinates retains every feasible persistent mode/initial-state/core witness. It is not necessary to select a complete architecture first and then search it for components.

## 3. Exact six-bit instance

Set n=6, H=4, and observe

    y(t) = (x_0(t) XOR x_1(t), x_3(t) XOR x_4(t)).

The five readouts are

    t=0: (1,1)
    t=1: (0,0)
    t=2: (1,1)
    t=3: (0,0)
    t=4: (1,1).

The task is to preserve the first parity in an autonomous component owning exactly three coordinates. Coordinates 0 and 1 are required by the task; the third coordinate p is unknown, with domain {2,3,4,5}. For each j construct the factor (p,theta_j) that excludes theta_j=1 precisely when j belongs to {0,1,p} but one of its neighbors does not. These factors follow from the proved local criterion.

The exact join calculation finds:

- 22 pairs (persistent mode vector, initial state) fitting all readouts;
- 17 distinct persistent mode vectors among those pairs;
- p=2, core {0,1,2}: seven pairs, five distinct modes;
- p=5, core {0,1,5}: seven pairs, five distinct modes;
- p=3 or p=4: no witness;
- both discovered cores required autonomous in the SAME mode vector and trace: no witness.

The size-three query gives a finite resource objective, not a supplied partition. Task preservation alone would allow the whole six-bit system. The returned alternatives are actual newly selected core boundaries within the declared universe.

## 4. Why the two discoveries cannot be combined

Autonomy of {0,1,2} forces theta_0=theta_2=0. Autonomy of {0,1,5} forces theta_1=theta_5=0. Requiring both therefore sets theta_0=theta_1=0. Then x_0 and x_1 are each constant forever, contradicting even the first observed change of their parity.

This obstruction is not a difficult search artifact: it has a short symbolic certificate derived from the local mechanisms and one readout transition. Separately existential certificates use different possible underlying mode assignments. Their conjunction must share the mode variables; copying them per request would invent a false joint realization.

## 5. Persistent nonlinear positive certificates

For core {0,1,2}, one witness is

    theta=(0,1,0,1,1,1), initial x=(1,0,1,0,1,1).

The local core dynamics are

    x_0'=x_0,
    x_1'=x_1 XOR (x_0 AND x_2),
    x_2'=x_2.

These are nonlinear and nonconstant. For example, with x_1=0, x_1' is one exactly when both boundary coordinates of this core are one. Thus the mechanism is not merely a static parity label. The exterior also has enabled nonlinear updates; the candidate model is not globally a product of independent bits.

For core {0,1,5}, one witness is

    theta=(1,0,1,1,1,0), initial x=(0,1,1,1,0,1).

Now x_1 and x_5 are constant and x_0'=x_0 XOR(x_1 AND x_5). Both initial witnesses fit the same five observed pairs.

For either core, the concrete certificate consists of the persistent mode assignments, ownership map, local update equations and hidden observed trace. The local equations prove the commuting state-projection square for every global state. Induction proves equality of projected executions for all later time. The finite trace proves only consistency with the provided data; it is not used as a substitute for the all-state equation.

The task parity is obtained by decoding the retained core state. It need not itself be a Markov state or an autonomous one-bit quotient: the extra retained coordinates are exactly the distinctions supporting its persistent dynamics.

## 6. Same-world parent certificates can still lose an interface-bounded crossing

Take the data-consistent model

    theta=(1,1,0,1,1,0), initial x=(0,1,0,1,0,1).

The component with coordinates {0,1,2} has one exterior input, x_5, while its complement {3,4,5} needs only x_2. The component with coordinates {0,1,5} has one exterior input, x_2, while its complement {2,3,4} needs only x_5. Hence each parent bipartition admits one-bit incoming interfaces at BOTH blocks in the SAME underlying model. These are nonautonomous but exact local mechanisms.

Their intersection {0,1} must update

    x_0'=x_0 XOR(x_5 AND x_1),
    x_1'=x_1 XOR(x_0 AND x_2).

Under a simultaneous one-way interface independent of the receiving current state, any exact incoming message needs at least two bits. Set x_0=x_1=1. The next pair is (1 XOR x_5, 1 XOR x_2), so four exterior pairs must receive four distinguishable messages. Arbitrary preprocessing of the exterior pair cannot evade that count.

Therefore parent certificates may share an actual model and nevertheless fail a demanded one-bit intersection interface. At two bits, the intersection is implementable. Direction and timing of communication remain part of the contract. The recurrent-selector note gives a scalable version and explains how query/reply or direct sensing changes such lower bounds.

Here one must not conflate two obstructions: section 4 has no shared model for the requested autonomous components; section 6 has a shared model but insufficient interface capacity for the requested crossing component.

## 7. Computation, representation size and verification

The implementation `check_hidden_ring_discovery.py` constructs primitive factors as above and performs exact joins and existential variable elimination. It does NOT first enumerate all complete worlds and feed that list to the join solver. A separate brute-force enumeration of 64 modes times 64 initial states independently checks the final answer.

For this instance, local elimination has a maximum intermediate scope of 19 variables and a maximum of 1,024 stored rows; it eliminates 24 hidden trace variables. The primitive transition factors have arity five. This explicitly shows why local physical wiring width alone does not imply a small discovery certificate or cheap checking: temporal reuse and shared modes increase the relevant width.

The program also tests 2,688 all-state retained-update equalities across the returned witnesses and checks the two-bit crossing lower-bound witness. Finite tests support, but do not replace, the general local autonomy and induction proofs.

For arbitrary n,H, the primitive factor description has O(nH) transition factors and constant transition table size. A complete positive mechanism-and-trace certificate has O(n+nH) bits before general interface tables are added. Checking a supplied certificate is linear in the number of primitive factor incidences here, plus checking the local ownership implications; all-time persistence follows from the proved local implication. Discovery remains exponential in the relevant elimination width in general. No uniformly bounded width, polynomial discovery, uniqueness, or statistical adequacy claim is made.

## 8. Relation to the typed decomposition framework

The readout view forgets the ownership boundary and many mechanism choices. It is not secretly a full-state model or a membership oracle. Concrete requested components are recovered as witnesses in a finite operational specialization of the certificate compiler. A specified-endpoint certificate refers to its selected actual model and local realization. Compatibility of the data summaries alone is weaker.

This dynamic specialization is distinct from the original graph C5 presentation. The original partition-forgetting quotient and identity-forest obstruction are proved in the main source-calculus note. This example supplies operational content to the certificate approach; it does not establish generation of arbitrary dynamic cells from the original C5 generators, which remains a separate obligation.

The six-bit instance is deliberately small enough to check independently. Its importance is the general locally compiled family, the actual discovery of alternative boundaries, persistent nonlinear certificates, and the two different joint-realization obstructions. It is not evidence that arbitrary robotic environments belong to this gate universe, nor a novelty claim for finite constraint elimination.
