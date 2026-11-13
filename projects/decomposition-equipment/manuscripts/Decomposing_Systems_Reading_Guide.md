# The decomposition problem behind the category theory

*A short reading path through the longer notes.*

The attractive idea behind an actegory is that a system and the things that act on it need not be packaged together. A group acts on a set; a monoidal category can act on a category. In the latter case the operator algebra can be represented by endofunctors of the system category. That division is useful because the operators have their own composition laws, independent of the details of every system on which they act.

It is natural to ask whether physical laws could be pulled out of dynamical systems in the same fashion. Sometimes they can. A symmetry transformation, a context extension, or a repeated resource operation may genuinely act on a class of models. But “physical law” also includes equations, constraints, variational principles, constitutive relations, conservation laws, and network connection rules. A resistance parameter may index a family of circuit models without representing a transformation that composes with other resistance changes. A constraint may specify which state and flow assignments are allowed, without determining a unique update. A variational principle selects stationary trajectories; it is not automatically an operator acting on arbitrary states.

This changes the original question. Instead of asking for a universal mechanism to vary laws, ask *which mathematical role is being varied and what is supposed to remain fixed*. An actegory handles law-as-operator. A fibration may organize families of models over law choices. An institution distinguishes law statements from models that satisfy them. Relation-based or jet-geometric descriptions accommodate constraints that have not been solved into state-update functions. Wiring-diagram formalisms hold an architecture fixed while components vary. These are different cuts through the system, not competing levels on a common scale.

## Why open systems become the decisive setting

For an isolated mathematical model, the distinction between its internal state and its external behavior can be left implicit. Interconnection makes that impossible. A component must advertise a boundary: what comes in, what goes out, when the exchange happens, what failures appear, and what other components may legitimately assume. The component could internally be an ODE, an automaton, a probability kernel, or a behavioral constraint on trajectories. It need not share the same internal representation as its neighbors.

But two components with identically shaped ports are not necessarily interchangeable. One motor may accept a command that overheats another; one solver may return an error while another diverges; one controller may require an internal measurement that is absent from the exposed boundary. A feedback connection can reveal distinctions hidden by ordinary forward input/output tests. The mathematical goal is therefore not simply to put components into boxes. It is to specify **which behavioral facts survive hiding and composition**.

A schematic architecture has an internal implementation, an interpretation as boundary behavior, and an operation that wires components together. The critical requirement is that interpreting the assembled implementation agree, in the intended sense, with assembling the boundary interpretations. That is a substantive property to prove, not a consequence of having chosen a fashionable categorical notation.

## Why restriction categories were an important discovery

A partial transition \(f:X\rightharpoonup Y\) comes with a domain on which it is defined. A restriction category packages the associated partial identity \(\bar f:X\rightharpoonup X\) and imposes equations that make it behave correctly under composition. In the familiar partial-function case,

\[
  D_{g\circ f}=\{x\in D_f:f(x)\in D_g\}.
\]

So the validity of a sequence is computed from the earlier transition *and* the precondition of the later one. This has an immediate application to open components with guards, local flow domains, or partial interfaces. It does not require maintaining an unrelated table of exceptions for every composite process.

Consider an actuator with hidden temperature \(\theta\) and a command that moves its shaft one unit while raising its temperature one unit. If the thermal limit is 2, the command is enabled only while \(\theta\le1\). Two consecutive commands are enabled only at \(\theta\le0\). A downstream module might also refuse to accept the new shaft position. The composed domain therefore differs from the actuator's local domain. Restriction algebra expresses that dependence cleanly.

The surprising limitation is equally instructive: **definedness is not the same thing as a controller-visible feasibility check**. A mathematical partial map can have an undecidable domain. A partially defined update says nothing about whether failure returns an error, blocks forever, or leaves partial physical effects behind. And a physically unsafe transition can be perfectly well-defined mathematically. Restriction categories provide a semantics of a chosen form of partial process; other aspects of failure need separate modeling.

## Where hidden state turns a local condition into an epistemic problem

Suppose the same actuator exposes shaft position but not temperature. Two internal states can produce the same observation, even though the move command is enabled in one and disabled in the other. There is no exact Boolean `enabled?(position)` test for that command unless the enabledness condition is constant across all states with the same readout.

A controller therefore has two different questions. The command is **possibly enabled** if at least one state compatible with its history allows it. It is **guaranteed enabled** if every compatible state allows it. A planner promising reliable execution needs the second notion, or a protocol for learning the hidden condition. For a multi-step objective the controller additionally needs a history-dependent policy, because an action that is individually available need not be part of any successful continuation.

This is the connection to modal and epistemic logics: the domain of a chosen transition supplies one proposition, but possibility, necessity, knowledge, and strategic controllability require further quantification over states, actions, outcomes, or policies. The original dream of revealing an environment's “semantics” by decomposing it becomes much more precise: the relevant object is a **boundary contract describing what can be observed, requested, guaranteed, and recovered under actual composition**.

## Why the unfamiliar mathematical techniques matter

Several less-common constructions become useful once the decomposition question has been stated precisely.

**Event structures** start from event occurrences, causality, and conflict rather than impose a single sequence of global states. They are valuable when concurrency and branch dependencies matter. Their configurations still function as states, but states are built from causal histories. They do not provide metric time or dynamics by themselves.

**Allegories** retain relations with converse, intersection, order, and a modular law. They are well suited to implicit constraints or nondeterministic behavior, where choosing an input/output function would discard multiplicity. **Kleisli categories** supply a different cut: a transition returns results with an effect such as nondeterminism, probability, partiality, or accumulated cost. Effect composition must be specified; it is not automatically interchangeable with relational composition or restriction structure.

**Diffeological and Frölicher spaces** change what counts as a smooth carrier. They can describe quotient, singular, or infinite-dimensional spaces that fit ordinary manifolds poorly. **Weil functors** probe infinitesimal structure; **jet bundles** organize the finite derivatives that a differential equation constrains; **Cartan distributions** express compatibility of derivative data with genuine solutions; and the **variational bicomplex** organizes field variations and differential identities. These answer different problems from the actegory problem: they factor the *geometry and differential content of physical laws*, not just operators from carriers.

**Dirac structures** separate power-conserving interconnection geometry from storage and dissipation laws, which is especially useful in physical networks. **Tulczyjew geometry** relates Lagrangian and Hamiltonian presentations without insisting on a globally invertible Legendre transform. Both are reasons to keep physical dynamics implicit when premature conversion to a vector field would erase degeneracies or constraints.

**Sheaves** organize local solutions and their compatibility on overlapping domains. **Stacks** retain isomorphisms between local objects—for example gauge equivalences—rather than require literal equality. **Derived solution spaces** retain nontransverse or infinitesimal information lost by taking only an ordinary set of solutions. These approaches become compelling when the problem is about gluing, symmetry, or deformation. They do not themselves synthesize an optimal continuation.

**Lenses, open games, and interaction semantics** explore still other boundary structures: forward observation with backward update, strategic play with equilibrium selection, or processes whose execution arises through feedback. Their usefulness depends on whether the external interaction really has those types, rather than on an assumption that all systems can be described as one generic category of actions.

## The design conclusion

A useful starting problem is deliberately small: take partial, deterministic open components with hidden state and typed ports; specify serial and parallel composition; decide which input/output/error traces a boundary exposes; and prove that the boundary interpretation is compositional. Then ask whether a particular refinement relation is preserved by the allowed interconnections. Feedback, stochastic effects, and law variation can be added after those obligations are explicit.

That construction would supply a testable version of the motivating idea. Internals could vary because they were interpreted through a stable, specified interface; substitutions would be licensed by refinement, not by port-name equality; and a controller would receive exactly the information and guarantees its decisions require. Failure of compositionality would reveal a missing distinction, such as hidden state, timing, error outcome, or feedback causality.

The governing principle is simple but demanding: **choose a decomposition by the information its boundary must preserve, not by the mathematical sophistication of the structures available**. The most valuable abstraction is the one that enables a needed composition or verification operation without silently deleting a distinction that changes the answer.

The [full connected notes](Decomposing_Systems_Connected_Notes.md) develop each of these techniques and the actuator example in greater detail.
