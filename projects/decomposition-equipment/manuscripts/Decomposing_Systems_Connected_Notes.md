# Decomposing dynamical systems without losing what they can do

*A connected set of working notes on laws, behavior, open interfaces, partiality, observation, and composition.*

## The question that holds the subject together

The starting attraction of an **actegory** is easy to state: instead of building a system and its transformations into one indivisible object, describe the transformations separately, describe the kinds of systems separately, and specify how the former act on the latter. That is a particularly satisfying way to factor a mathematical theory. It makes one ask whether a different force law, resource budget, symmetry, or environment can be supplied without rebuilding everything else.

But it immediately exposes a deeper question. *What is being separated from what?* A law of motion is not the same kind of thing as a physical constraint. A sensor is not a weakened law of motion. An interconnection changes neither a component's state space nor its equations in quite the same way that changing a constitutive relation does. An error, an illegal command, a violated safety requirement, and a physically impossible trajectory are different phenomena, even when software reports all of them as “failure.”

The conversation eventually arrived at a more demanding problem than finding one elegant categorical tool:

> Build a large system out of open components whose internal descriptions may vary substantially, while making explicit what each component exposes, what an observer or controller can do with that information, and which assertions remain valid after the components are connected.

That problem has two sides. There is **freedom of internal modeling**—one component might be an ODE, another an automaton, another a probabilistic relation, another a constraint on complete trajectories. And there is **discipline at the boundary**—components cannot be substituted or interconnected merely because their ports have the same names. A connecting system can be sensitive to enabled commands, hidden state, timing, failure, causal order, and feedback behavior.

The useful mathematical techniques are therefore not rungs of one ladder. Each offers a particular *cut* through the system: operator/carrier, law/model, state/behavior, internal/boundary, defined/undefined, observed/hidden, local/global, or energy/interconnection. The question is whether that cut preserves what a later piece of reasoning needs.

### A running example: an actuator as an open component

Imagine a position actuator with an internal temperature. It accepts a motion command, moves its shaft, and returns a position readout. In the simplest discrete toy model its internal state is 

\[
  s=(x,\theta),
\]

where \(x\) is position and \(\theta\) is temperature. For a command \(u\), suppose the nominal update is

\[
  (x,\theta)\longmapsto (x+u,\theta+u^2).
\]

Take allowable commands to be \(u\in\{0,1\}\) and impose \(\theta+u^2\le 2\) as the operational limit. The position readout is \(r(x,\theta)=x\); temperature is not directly exposed.

This little system can be considered in many mathematically different ways. The update is a partial function if a disallowed command simply has no transition. It is a total function into a result-or-error type if the actuator reports a thermal fault. Its admissible trajectories form a behavior. Its position and temperature are state variables; a controller seeing only position has an information problem. Connecting its output to a second component imposes downstream preconditions. Replacing its heating law changes the domain of future commands. Closing a feedback loop introduces its own timing and solvability issues.

None of these descriptions is “the semantics of the actuator” in the singular. Each answers a different question. This example will recur because it makes the boundaries between the techniques concrete.

---

## 1. Actegories: separate an algebra of operators from what it operates on

The analogy with group actions is the right point of entry. A group \(G\) can act on a set \(X\), making \(X\) a \(G\)-set. Replace the group with a monoidal category \((\mathcal V,\otimes,I)\), the set with a category \(\mathcal C\), and action equations with coherent natural isomorphisms. The result is an actegory, given by

\[
  \odot:\mathcal V\times\mathcal C\longrightarrow\mathcal C,
\]

and coherence such as

\[
  (v\otimes w)\odot c\cong v\odot(w\odot c),
  \qquad I\odot c\cong c.
\]

Equivalently, one has a **strong monoidal functor**

\[
  \mathcal V\longrightarrow\operatorname{End}(\mathcal C),
\]

where the objects of \(\operatorname{End}(\mathcal C)\) are endofunctors and its monoidal product is functor composition. This equivalence captures the appeal: an external operator algebra is *represented* as transformations of the carrier category. Crucially, an action functor also acts on morphisms. It is more than a family of unrelated transformations of objects.

The payoff is not merely tidy notation. Suppose a family of context changes must be applied repeatedly, and applying context \(v\) after \(w\) must agree—up to specified coherent isomorphism—with applying their composite. Rather than re-establishing the composition law for every model individually, the action packages that obligation into a reusable structure.

### When the factorization is genuinely useful

There are at least three common situations:

**A reusable operator calculus.** Several kinds of systems admit the same family of context changes, resource extensions, symmetries, or transformations. Keeping that algebra separate allows its laws to be stated once.

**Controlled variation.** A class of systems can be systematically modified by operators with known composition rules. Such operations are not automatically arbitrary replacements; they are changes licensed by the action.

**Multiple operator families.** Time evolution, symmetry changes, and resource accounting may each have their own algebra. Instead of one undifferentiated “law,” one can ask how their actions interact.

The third is interesting but easy to overstate. Having

\[
  \mathcal V\curvearrowright\mathcal C,
  \qquad \mathcal W\curvearrowright\mathcal C
\]

does not say the two actions commute. To commute, they need a coherent interchange comparison between \(v\odot(w\star c)\) and \(w\star(v\odot c)\). They might instead interact noncommutatively, require a distributive law, or be impossible to combine in the intended way.

For example, the vector fields \(V=\partial_x\) and \(W=x\partial_y\) on \(\mathbb R^2\) generate flows

\[
\Phi_t^V(x,y)=(x+t,y),\qquad
\Phi_s^W(x,y)=(x,y+sx).
\]

Their order changes the final \(y\)-coordinate by \(st\). Treating them as “two independent directions of variation” would erase exactly the interaction that matters.

### Why not every physical law is an action

A parametric family of models, such as changing a resistance \(R\) in \(v=Ri\), does not automatically define a monoidal action of resistance values on circuit models. The parameters may have no composition law corresponding to successive application. Likewise, a vector field on a manifold specifies infinitesimal dynamics; it does not, simply by existing, act as an endofunctor on a category of systems. A flow might not even exist globally.

This distinction separates three attractive but nonidentical ideas:

1. A **time monoid acts on one state space**, as in \(\phi_{t+s}=\phi_t\circ\phi_s\).
2. A **parameter indexes a family of dynamical laws**, as in \(\dot x=f_\lambda(x)\).
3. A **monoidal category acts on a category of systems**, changing objects and morphisms coherently.

An actegory is the third construction. A model may use the first or second without supplying it.

**Working intuition:** reach for an actegory when “these operators repeatedly transform these kinds of systems, and their composition matters” is already a meaningful claim. Do not start by forcing every external influence into an action; first determine whether the operators really have the needed algebra.

---

## 2. The word “law” conceals several different interfaces

The desire to “factor physical laws out of dynamical systems” becomes sharper after distinguishing what a law *does in the model*. Several objects described informally as laws have different input and output types.

Consider a simple electrical network. A resistor law relates voltage and current: \(v=Ri\). A capacitor law relates current to the rate of change of voltage: \(i=C\dot v\). Kirchhoff laws constrain which voltage and current assignments are compatible at the network level. A switch changes the allowed connections. A thermal safety rule limits which operating points are licensed. A voltage sensor determines what is known to a controller. These cannot all be varied by the same generic “replace an update map” operation.

It is more revealing to ask what kind of mathematical role each statement occupies:

| Role of a law | Typical representation | What it leaves open |
|---|---|---|
| Evolution | \(s'=f(s,u)\), or \(\dot s=f(s,u)\) | Existence of solutions, admissible inputs, observations |
| Constraint / constitutive relation | \(R\subseteq X\times Y\), or \(F(x,y)=0\) | Which variables are inputs, uniqueness, solvability |
| Variational selection | Action functional on paths plus a stationarity rule | Boundary conditions, variation class, singularities |
| Symmetry | Group or category action with invariance/equivariance law | Which quantities transform or remain invariant |
| Conservation | Quantity constant along admissible evolution | Why the dynamics preserve it |
| Parameter dependence | Family \(f_\lambda\) or family of models \(M_\lambda\) | Which comparisons between parameters are meaningful |
| Interconnection | Wiring constraints and composition rules | Whether the connected equations are well posed |
| Measurement | Readout map or observation kernel | Which hidden distinctions are recoverable |

This is not a classification of physics itself. A single equation can play more than one role depending on how the surrounding model is constructed. For example, an implicit constitutive relation can sometimes be solved for current as a function of voltage; in another operating regime it can have multiple branches and no globally defined function. Treating it as a function too early deletes that distinction.

One consequence is that **varying laws freely** is not a single mathematical operation. At a minimum, separate:

- **Parameter variation:** same kinds of equations, changed constants. The carrier and wiring often stay fixed.
- **Theory variation:** changed admissibility conditions or equations, possibly changing the class of models.
- **Semantic variation:** changed type of behavior, for example a deterministic map replaced by a nondeterministic relation.
- **Architecture variation:** changed connections between components, which may change the global state space and feasible trajectories.

The distinction pays for itself when designing reusable models. Changing a coefficient might be implemented by reindexing a model family. Making a constitutive law multivalued changes the process semantics. Replacing a sensor changes information available to the controller. Rewiring a circuit changes the algebra of assembly. No unifying notation should conceal those different consequences.

### Indexing laws: fibrations and institutions

An **indexed category** or **fibration** handles one natural problem: systems live *over* choices of parameters, contexts, or theories. In a fibration \(p:\mathcal E\to\mathcal B\), the objects over \(b\in\mathcal B\) form a fiber \(\mathcal E_b\). The base describes changes of context; the fibers describe what is modeled at a given context. The usual fibration reindexing along \(u:b\to b'\) runs contravariantly, \(u^*:\mathcal E_{b'}\to\mathcal E_b\). This is not automatically an algorithm that changes a physical law forward in time. It is a precisely typed way of relating descriptions under changes of base.

An **institution** makes a different cut. It distinguishes a signature of symbols, the sentences that can be written in that signature, the models interpreting those symbols, and the satisfaction relation \(M\models_\Sigma\varphi\). Its key condition says that changing notation/signature commutes appropriately with translating sentences and reducing models. That is attractive when the object to be varied is a *theory of laws*, not an operator acting on a system.

An actegory, a fibration, and an institution are thus not three competing levels of generality. They answer distinct questions:

- **Actegory:** How does an algebra of operators act on systems?
- **Fibration:** How are classes of systems organized over choices of context or parameters?
- **Institution:** How are law statements related to models that satisfy them, even as the signature changes?

A model family may need all three. But writing their names next to one another does not construct the compatibility maps between them. Those maps are where the actual factorization work lies.

---

## 3. Before decomposing a state machine, ask whether the state machine is the right starting point

Much of the usual theory of dynamical systems begins with states and a transition rule. Two alternatives help expose what that choice assumes.

### Coalgebras: retain state, abstract the form of behavior

A coalgebra for an endofunctor \(F\) is a map

\[
  c:S\longrightarrow F(S).
\]

The state carrier \(S\) is explicit; \(F\) specifies what an observation/step of behavior looks like. For example, \(F(S)=O\times S^I\) describes a Moore-style machine with an output and an input-indexed next-state function. The type \(F(S)=(O\times S)^I\) describes a Mealy-style update whose output and successor can depend on the current input. A powerset-like functor gives nondeterministic successors; an appropriate distribution functor gives stochastic successors.

The attractive decomposition is **carrier + behavior type + particular coalgebra**. One can study morphisms preserving that structure, behavioral equivalence, and, where final coalgebras exist, abstract observable behavior. Choosing \(F\) is substantive: it fixes what counts as a step or observable output. Different functors are not automatically interchangeable while retaining the same semantics.

For the actuator, a coalgebraic representation naturally includes the state \((x,\theta)\) and a choice of how commands and outputs appear in each step. This retains a mechanism that can explain future transitions.

### Behavioral systems theory: remove the privilege of internal state

The approach associated with Willems starts at the other end. Specify a set of admissible trajectories

\[
  \mathcal B\subseteq W^T
\]

for a signal alphabet/space \(W\) and time domain \(T\). Equations constrain trajectories, but the system need not come equipped with a preferred distinction between input and output, or even an explicit state representation.

This is useful when the natural statement of a physical law is relational: Kirchhoff constraints, coupled differential-algebraic equations, boundary constraints, or networks whose variables become inputs or outputs only after interconnection. A state-space realization may be one *implementation or presentation* of the behavior, not the definition of the system.

There is an important compositional operation here. If component behaviors concern signals \((x,m)\) and \((m,y)\), wiring them along the shared signal \(m\) gives the external behavior

\[
\mathcal B_{\mathrm{ext}}
 =\{(x,y):\exists m\;[(x,m)\in\mathcal B_1\ \land\ (m,y)\in\mathcal B_2]\},
\]

with the equations interpreted over complete, compatible trajectories. Internal wire signals are then *hidden by existential projection*. This is an illuminating contrast with simply composing two functions. In algebraic or physical networks, one often solves a joint constraint rather than executing one component and then another.

The tradeoff is also important. A set of external traces can forget internal causal structure, distinguishable hidden configurations, termination behavior, or how a component behaves when placed in feedback. Whether it is adequate depends on the contexts in which the component will be used. Behavioral equivalence under one exposed signal set is not automatically substitutability under every form of connection.

**Selection principle:** coalgebra is compelling when the representation needs explicit state and a reusable notion of step; behavior-first modeling is compelling when a law is primarily a constraint on possible signals and state/input–output choices are secondary. Both are valid decompositions. They preserve different information.

---
## 4. Open systems: a component is more than its internal equations

The next move is to stop considering an isolated dynamical system. A large system consists of components connected at interfaces: a physical plant sends measurements to a controller; the controller sends commands to an actuator; an actuator interacts with a load; a safety monitor can disable a command. Each component may use a different internal mathematical language.

A schematic deterministic, discrete-time component is

\[
  \delta_C:S_C\times I_C\rightharpoonup S_C\times O_C,
\]

with hidden state \(S_C\), inputs \(I_C\), and outputs \(O_C\). The partial arrow is only one possible process semantics. It could instead be a relation, stochastic kernel, continuous-time system, or set of admissible trajectories. An observation map may be part of \(\delta_C\)'s outputs or an additional channel with its own timing.

A **boundary type** has to say what can actually be connected. It may describe port names and data types, but also whether a port is an input or an output, the flow of time, a protocol, a power convention, or a shared conservation constraint. A **component specification** additionally says which behaviors can occur at that boundary. A **contract** says what surrounding systems are allowed to assume and what the component guarantees under those assumptions.

These are three different levels:

- **Can be wired:** interfaces are structurally compatible.
- **Has composite behavior:** the connected component equations or operational rules determine some behavior, perhaps with multiple solutions or none.
- **Meets a system-level requirement:** that composite behavior satisfies a chosen safety, liveness, or performance condition.

The first does not imply the second, and the second does not imply the third.

### What the familiar wiring formalisms contribute

Decorated or structured cospans distinguish an interface from internal apex data and supply principled forms of network composition. Operads and wiring-diagram calculi describe allowable assembly shapes and how smaller systems occupy the slots of larger ones. Polynomial functors can describe families of interaction positions and directions—useful for interactive systems with a typed shape of observations and responses. Symmetric monoidal categories handle serial and parallel composition when the semantics fits those operations. Double categories or equipments become attractive when interconnection and interface change/refinement must coexist as different kinds of morphisms.

None of these names determines a universal semantics for a plant or controller. They supply a **syntax or algebra of connection**, which must be interpreted in a compatible process model. For example, the same wiring diagram may be interpreted as a network of functions, differential-algebraic equations, stochastic components, or temporal processes. Whether each interpretation is well posed is an additional issue.

### Serial composition when internal state is retained

Let

\[
 f:S_A\times I\rightharpoonup S_A\times M,
 \qquad
 g:S_B\times M\rightharpoonup S_B\times O.
\]

The connected system has joint state \(S_A\times S_B\). On input \(i\), it runs \(f\) on \((s_A,i)\), obtaining \((s_A',m)\), and then runs \(g\) on \((s_B,m)\), obtaining \((s_B',o)\). Its step maps \(((s_A,s_B),i)\) to \(((s_A',s_B'),o)\) **only when both substeps are defined**.

Notice what makes this operation precise. The intermediate signal \(m\) must be produced by the first component and accepted by the second. The hidden states are not thrown away. Both domains of definedness matter. Simply writing \(g\circ f\) without accounting for the two state carriers would obscure the types.

For a physical network coupled through simultaneous equations, serial execution may be the wrong interpretation entirely. Interconnection may instead amount to solving a joint relation. That is why choosing the wiring semantics precedes stating the composition theorem.

### The attraction and limit of local contracts

Suppose module \(A\) guarantees an output magnitude at most 3 whenever its input magnitude is at most 2. Module \(B\) accepts inputs only up to magnitude 3. This looks compatible. But if they share a power budget, run asynchronously, have stateful rate limits, or form a feedback loop, the simple magnitude conditions may be insufficient. Their contracts need to specify every property on which the next component or the system-level guarantee relies.

An **assume/guarantee** calculation has the rough form: local guarantees discharge the assumptions of connected components; under explicitly proved compatibility conditions, the composed component satisfies a derived global contract. There is no unconditional law that valid local components form a valid global one. The compatibility premises carry the work.

---

## 5. Restriction categories: give partial behavior an algebra

The less familiar idea that connects especially well to open components is the **restriction category**. Its appeal is that the meaning of a map can include *where it is defined*, and definedness follows coherent laws under composition.

Start with partial functions. A partial function

\[
  f:X\rightharpoonup Y
\]

has a domain \(D_f\subseteq X\). Associated to it is the partial identity

\[
  \bar f:X\rightharpoonup X,
  \qquad \bar f(x)=x\ \text{for }x\in D_f,
\]

undefined elsewhere. A restriction category abstracts this \(f\mapsto\bar f\) operation through equations that work without referring to elements or literal subsets. Its archetype is the category of sets and partial functions.

The immediate compositional fact is

\[
  D_{g\circ f}=\{x\in D_f:f(x)\in D_g\}.
\]

A multistep action can be attempted successfully only where its first step works *and* the first step's result lies in the next step's domain. This is much richer than separately storing Boolean flags saying that individual components are valid somewhere.

### Back to the actuator

For the thermal actuator, fix a command \(u\). The partial update is

\[
 a_u(x,\theta)=(x+u,\theta+u^2),
 \qquad D_{a_u}=\{(x,\theta):\theta+u^2\le2\}.
\]

If \(u=1\), a single move is enabled for \(\theta\le1\). Two consecutive moves are enabled only when \(\theta+2\le2\), i.e. \(\theta\le0\). If we also require \(\theta\ge0\), the two-move plan is defined only at initial temperature zero. That conclusion is computed from the *effect of the first move* and the *precondition of the second*, not from a separate hand-written exception list.

Now add a downstream module \(g\) that accepts shaft positions only when \(x\le1\). An actuator step might be internally enabled yet produce \(x'=2\), which the downstream module rejects. Wiring changes the domain of the composite without changing the original actuator's domain.

This is the concrete mathematical payoff: applicability is no longer an annotation that someone might forget to propagate. Under partial-function composition, it participates in the algebra.

### Four things definedness does *not* tell us

The word “validity” is dangerously overloaded here.

**Definedness is not safety.** A deterministic update may be mathematically defined and still enter an unsafe region. One may *choose* to restrict the map to safe inputs, but then the restriction encodes a selected safety policy, not a theorem that the original dynamics lacked those transitions.

**Definedness is not empirical model validity.** A low-speed approximation may evaluate perfectly well outside the speed range where it predicts reality accurately. To treat validity of the approximation as a domain restriction, a modeler must provide that region or an evidential criterion for it.

**Definedness is not an executable guard.** The existence of \(\bar f\) as a partial identity does not imply a terminating algorithm \(\texttt{enabled?}(x)\). For partial computations, deciding definedness may itself be undecidable. If an API must return a Boolean guard, that is extra computational structure.

**Undefinedness is not a classified failure.** A partial map contains no result outside its domain. It does not say whether the real system rejects a command, throws an error, changes state and then faults, hangs, or violates a requirement. To model those distinctions, introduce explicit failure outcomes, effects, or execution traces.

In particular, a composite partial function being undefined does **not** imply that earlier physical effects were rolled back. A plan that moved a motor before failing needs an execution-prefix semantics if recovery depends on the motor's new position.

### Restriction structure and modal reasoning touch, but do not coincide

For a deterministic partial action \(f\) and predicate \(Q\subseteq Y\), the dynamic-logic diamond is

\[
  \langle f\rangle Q
   =\{x\in D_f:f(x)\in Q\}.
\]

Thus \(\langle f\rangle\top=D_f\): being able to execute \(f\) successfully is a particular modal proposition. The box, under the usual relational semantics, is

\[
  [f]Q=(X\setminus D_f)\cup\langle f\rangle Q.
\]

The box is vacuously satisfied where no execution exists, whereas the diamond requires successful execution. They are not globally equal even for deterministic partial programs. A restriction idempotent and an enabledness predicate correspond in the familiar partial-map setting, but their types are different: one is an arrow, the other a predicate.

This makes restriction categories relevant to the question “what does this particular process permit here?” A modal layer asks richer questions: could *some* action reach \(Q\); will *all* possible successors satisfy \(Q\); can an observer know that the action is enabled; or does a policy exist that forces success? Those questions need actions, observations, quantifiers, and—often—temporal or strategic semantics beyond restriction alone.

### A subtle constraint on mixing restrictions with actegories

Suppose an external context acts on a restriction category by **restriction-preserving endofunctors** \(F\). If \(f\) is total, then

\[
  \overline{F(f)}=F(\bar f)=F(1_X)=1_{F(X)}.
\]

So these functors preserve totality. This is excellent if an operator is intended to preserve a process's notion of definedness, but not if “changing the law” is supposed to make a formerly total operation partial *on the same unchanged carrier*. Such law changes need a different representation or a more nuanced comparison of validity domains.

This is an instructive instance of the larger theme: algebraic structure buys laws and reuse precisely by **constraining which variations are legal**. It cannot simultaneously guarantee those laws and allow arbitrary incompatible variation.

---

## 6. The observation boundary: possible, enabled, known, and controllable are different

The most consequential turn comes when the component's internal model is hidden behind a sensor or controller API.

The actuator's actual state is \((x,\theta)\), but the controller reads only \(x\). Consider two states

\[
  s_0=(0,0),\qquad s_1=(0,2).
\]

They have the same readout: \(r(s_0)=r(s_1)=0\). Command \(u=1\) is enabled at \(s_0\), but not at \(s_1\). An internal definedness predicate exists; nevertheless, no Boolean predicate depending only on the instantaneous readout can reproduce it exactly. The boundary has erased a distinction relevant to execution.

This is not an edge case. It is typical whenever sensors expose less than the state required by guards, safety checks, or future dynamics. The observer may still infer a state from history, but that inference belongs to the observation model and available actions, not to the instantaneous readout map alone.

### May versus must

Let \(B_h\subseteq S\) be the **nonempty** set of states compatible with an observation/action history \(h\). Then for a command with domain \(D_a\):

\[
  \operatorname{MayEnabled}_a(h)
   \iff B_h\cap D_a\ne\varnothing,
\]

\[
  \operatorname{MustEnabled}_a(h)
   \iff B_h\subseteq D_a.
\]

The first says the action is enabled in *some* currently possible state; the second says it is enabled in *every* state still possible. In a standard knowledge interpretation, the second is what licenses the claim that the observer **knows** the command is enabled. This assumes the information set correctly represents the available evidence; it does not supply an algorithm for computing that set.

For the actuator with history compatible with both \(s_0\) and \(s_1\), the command \(u=1\) is may-enabled but not must-enabled. A controller promising to issue only guaranteed enabled commands cannot send it yet. A controller allowed to gamble or use a fault-reporting protocol might. They have different contracts even if they are connected to the same hardware.

### When can an exact observable command exist?

There is a useful exact criterion. Let \(r:S\to O\) be surjective onto attainable observations, and let \(f:S\rightharpoonup S\). Seek a partial function \(\widehat f:O\rightharpoonup O\) satisfying

\[
  \widehat f\circ r=r\circ f.
\]

Such an observable command exists **if and only if**:

1. **Domain saturation:** if two states have the same observation, either both allow \(f\) or neither does.
2. **Output consistency:** whenever \(f\) is enabled at two states with the same observation, the resulting states have the same observation.

Necessity follows by comparing domains and outputs of the two sides of the equation. For sufficiency, define \(\widehat f(o)\) using a representative state with readout \(o\); the two conditions ensure the definition is independent of that choice.

This is an important antidote to a tempting but false shortcut. An internal command does not automatically “descend” to a command on observations. When these conditions fail, the boundary-level description must retain more information—for example, belief states or observation histories—or permit nondeterministic/probabilistic observable behavior.

### Controllability has another quantifier trap

Even perfect knowledge that *some safe action exists in each possible state* is weaker than having a safe action that can actually be chosen from the available observations. Compare

\[
  \forall s\in B_h\;\exists a:\operatorname{Safe}(s,a)
\]

with

\[
  \exists a\;\forall s\in B_h:\operatorname{Safe}(s,a).
\]

The first allows a different action for each hidden state. The second requires one action that works for all states compatible with the current information. If two indistinguishable states require opposite emergency commands, statewise controllability does not give observation-based controllability.

For a multi-step objective, even the second statement is only a local test. A controller needs a policy that chooses actions from permitted histories, and feasibility must hold across future observations, constraints, and adversarial or stochastic outcomes.

### Why an API is a semantic surface

An interface is not exhausted by `command(input) -> output`. A real controller contract may expose: which commands can be issued, which can be known to be enabled, what happens when they are not, what errors reveal, what timing is guaranteed, whether state changes before an error, and which future actions remain feasible. Some of this can be described with restriction predicates; other parts require error effects, epistemic structure, temporal logic, or game/strategy semantics.

The general problem of decomposing a large system can now be stated more precisely: **internal distinctions can be hidden only when doing so preserves the decisions and guarantees required of the external users of that component.**

---

## 7. When processes are relations, probabilities, or other effects

Partial functions are still a restrictive process model. One input has at most one successful result. A component may instead have several admissible successors, noisy outputs, weighted costs, or stateful side effects.

### Relations and allegories: do not choose an output variable too early

Suppose a constitutive law is given by

\[
  F(v,i)=0.
\]

It describes a relation between voltage and current. Unless the relation defines a unique current for every permitted voltage, there is no globally defined map \(v\mapsto i\). Choosing an input–output orientation can require solving an equation and may lose multiplicity or branch information. Relation-first modeling retains that information.

An **allegory** generalizes a calculus of relations with an order on arrows, binary meets, converse, and a modular law. In the ordinary relational model, these correspond to inclusion, intersection, reversal of a relation, and relational composition. The converse \(R^\circ\) of a process relation is a mathematical reversal of pairs; it is not necessarily a physically available inverse process. Allegories are attractive when constraints and bidirectional reasoning are more primitive than functions.

Relations also handle nondeterministic steps. But the distinction between **may** and **must** then becomes internal to the process itself, not only to an observer's ignorance. A state may have several possible successors even when fully known.

One caution matters if restriction categories are added. It is tempting to define the restriction of any relation as the partial identity on inputs having **at least one** outgoing related value. That does not generally satisfy restriction-category axioms. For example, let one input relate to both \(0\) and \(1\), while a following relation accepts only \(0\). The existential domain of the composite contains the input, but restricting the first relation *before* the second removes the branch to \(1\), whereas a domain restriction of the whole composite leaves both first-step branches available. The required equation fails. One must choose a compatible relational effect theory, not reuse the partial-function proof by renaming terms.

### Kleisli semantics: package the nature of an effect

For a monad \(T\), a Kleisli arrow \(X\to Y\) is represented by a map

\[
  f:X\longrightarrow T(Y).
\]

Different \(T\)'s express different kinds of computation: a powerset construction for nondeterministic results, a suitable distribution monad for stochastic results, a maybe/option construction for partiality, or a writer construction for accumulated logs and costs. Kleisli composition prescribes how those effects propagate through sequential steps.

For a stochastic actuator, the heating increment might be uncertain rather than exactly \(u^2\). A kernel assigns a probability distribution to successor states. The ordinary probability distribution kernel preserves total mass. Representing failure as “leaked probability” requires an explicit subprobability interpretation, absorbing error state, or other chosen effect. Zero reward and missing reward are likewise not the same thing as failure.

Combining effects is another nonfree step. A model with nondeterminism *and* probability needs to say whether nondeterministic choices are made before random outcomes, what information an adversary receives, and how probability distributions over possible branches compose. Different answers can produce different planning and verification results.

### Weighted relations and quantaloid-enriched thinking

A plain relation records whether a connection exists. A weighted relation can assign cost, possibility degree, or another value to each pair. Composition then combines weights along intermediate states and aggregates alternative paths. In familiar choices of semiring or quantale, the same abstract pattern supports shortest paths, reachability, and other path calculations.

The payoff is compositional accounting, not a universal theory of numerical scores. Choosing min-plus cost, max-min possibility, ordinary Boolean truth, or probability changes the meaning of aggregation. Probabilities in particular need normalization and dependence information that generic weighted-path arithmetic need not preserve.

**Working distinction:** use partial functions for deterministic updates with domains; relations for constraints and nondeterministic outcomes; kernels for probabilistic laws; algebraic effects for failures/resources; and richer relational calculi when converse, order, and intersection are operations that downstream reasoning genuinely needs.

---
## 8. Feedback changes the meaning of composition

Open components are often discussed as though wiring them were just function composition. Feedback is where that simplification becomes visibly inadequate. An output may be routed back to an input of the same network. The composite must then specify not only which ports are connected but what it means for the loop to execute.

For an **instantaneous** feedback interpretation, suppose a component is represented by

\[
  F:X\times U\rightharpoonup Y\times U.
\]

A closed-loop input–output relation might be defined by

\[
  (x,y)\in\operatorname{Fb}(F)
  \iff \exists u\; F(x,u)=(y,u).
\]

The internal wire value \(u\) must solve a consistency equation. The solutions may be absent, unique, or multiple. If \(X\) is a singleton and \(U=Y=\{0,1\}\), then

- \(F(*,u)=(u,1-u)\) has **no** consistent feedback value.
- \(F(*,u)=(u,u)\) has two consistent values with **different external outputs**.

In the first case the feedback relation is empty; in the second it is multivalued. Neither is an ordinary total function. Even where a feedback solution exists, a unique *internal* solution is not always necessary for a unique *external* result—different internal witnesses might lead to the same output. These possibilities need an explicit choice of semantics.

### Delayed feedback is a different problem

A loop with a one-step delay need not solve an instantaneous fixed-point equation. For example, \(u_{t+1}=1-u_t\) is a perfectly defined discrete-time oscillator once its initial state is supplied. Calling its oscillation an “undefined feedback computation” would be a category error. In continuous control, closed-loop existence may depend on Lipschitz or other regularity conditions, and a well-defined closed loop may still be unstable. Well-posedness, stability, safety, and performance are distinct obligations.

A **traced monoidal category** abstracts certain kinds of feedback, subject to trace laws. But there are two quite different senses of partiality here: a trace operation itself may exist only for some arrows, or the trace may be total as an operation while its resulting arrows denote partial processes. Neither follows merely from the existence of a restriction category. Likewise, the availability of a trace does not establish the physical or operational well-posedness of a particular loop without an appropriate interpretation.

This is one reason a component boundary cannot always be summarized by ordinary input/output behavior. Two components may agree on their unconstrained external input/output relation and behave differently when inserted into feedback contexts. If feedback is an allowed consumer operation, any notion of substitutability has to account for it.

**Practical test:** before black-boxing a component, ask whether the surrounding system can connect its outputs back to its inputs; whether the loop has a delay; and whether the chosen behavior model retains the causal, temporal, or fixed-point information needed for that connection.

---

## 9. Event structures and causal organization: when the global sequence is the wrong abstraction

A conventional transition system represents behavior as a sequence of states. That is often convenient, but the sequencing may encode an artifact of the representation rather than a real dependency. Independent sensor readings or distributed transactions can occur without one naturally preceding the other. A single global clock also makes asynchronous systems look more synchronized than they are.

An **event structure** starts from occurrences and their relations. In a prime event structure, one typically has

\[
  (E,\le,\#),
\]

where \(E\) is a set of events, \(\le\) is causal dependency, and \(\#\) is conflict. If \(e\le f\), event \(e\) must already have happened before \(f\) can occur. If \(e\# f\), they cannot both belong to the same execution. Conflict is normally required to be hereditary with respect to causality, and appropriate finiteness assumptions are often imposed.

A **configuration** is a causally downward-closed, conflict-free collection of events representing one consistent stage or execution prefix. Thus state has not disappeared; it has been reconstructed as accumulated causal history rather than postulated as a tuple of variable values.

### An example that a global trace obscures

Imagine a machine that must complete a safety check \(a\) before energizing a motor \(b\), while a second sensor records an independent reading \(c\). A linear log might show \(a,c,b\) or \(c,a,b\). Those traces differ, but the underlying causal structure may be the same: \(a\le b\), with \(c\) independent of both. Event semantics records the dependency and avoids asserting that the arbitrary order of the independent readings has operational meaning.

Conflict adds branching: if two alternative commands \(d\) and \(e\) exclude each other, both cannot occur in a single configuration. Incomparability is not by itself concurrency; two incomparable events can also be in conflict. True concurrency requires the relevant compatibility as well as the lack of an imposed causal order.

Event structures are compelling for distributed control, asynchronous workflows, protocol verification, and systems where retaining the causal origin of choices matters more than assigning a single total order to all events. They do **not** supply metric elapsed time, durations, or a numerical physical evolution law without further structure.

### Causal order in a broader setting

Causal sets, causal categories, and causal sites also privilege influence or precedence over a global time coordinate, but these terms do not denote one interchangeable theory. A causal site, for example, includes relations between spacetime regions and additional structural axioms; it is not merely any poset with arrows interpreted as influence.

The conceptual payoff is nevertheless recognizable: causal structure can be treated as primitive while coordinate time, simultaneous state slices, and propagation models become subsequent choices. This matters most in relativistic, asynchronous, or event-oriented models. It does not eliminate dynamics; it changes the substrate on which dynamics must be specified.

---

## 10. Diffeological and Frölicher spaces: loosen the state-space geometry

Another hidden commitment in standard dynamics is the use of a smooth manifold. Manifolds are excellent when a state space locally resembles \(\mathbb R^n\), but quotient spaces, singular strata, spaces of functions, and some configuration spaces do not fit that assumption comfortably.

A **diffeological space** retains an underlying set \(X\), but takes its smooth parameterized plots \(p:U\to X\), for open \(U\subseteq\mathbb R^n\), as primitive data. The plots satisfy closure under precomposition with ordinary smooth maps, locality, and inclusion of constant plots. A map between diffeological spaces is smooth when it carries admitted plots to admitted plots.

A **Frölicher space** starts instead with a compatible pair of smooth curves into \(X\) and smooth real-valued functions out of \(X\), each determining the other by composition. Both approaches expand the possible substrates of smooth mathematics, but their definitions and resulting structures should not be silently identified.

### What the decomposition buys

The familiar decomposition “state space = manifold plus differential law” becomes “state carrier + chosen notion of smoothness + a law expressed in that smooth structure.” The smooth structure can be tailored to spaces with singular or infinite-dimensional behavior that resist ordinary charts.

For instance, suppose the actual state of a mechanical system is a configuration modulo a symmetry. The quotient may have points with different stabilizers and fail to be an ordinary manifold. The quotient diffeology can still record which parameterized motions count as smooth without deleting the quotient. In some applications this is preferable to artificially choosing a chart near each regular stratum and ignoring singular configurations.

But there is an important stopping point. Having a meaningful notion of smooth curve \(\gamma:\mathbb R\to X\) does not automatically define its derivative in the required dynamical sense, specify a vector field, or guarantee existence and uniqueness of trajectories. The appropriate tangent construction and differential equation theory must be selected separately. Generalized smoothness is not a complete dynamics engine.

This technique is most interesting when the **carrier geometry itself** is the source of unwanted constraints. If the existing manifold category already captures the intended states and operations, moving to diffeology adds flexibility without necessarily adding useful control or composition results.

---

## 11. Weil functors, jets, and differential equations as geometric constraints

The next set of ideas addresses a different kind of factorization: separating the local *differential information* in a law from its global solutions. This is especially attractive when varying physical laws means changing derivative constraints, not adding an operator to a system.

### Weil functors: different infinitesimal probes

A real Weil algebra is a finite-dimensional commutative local \(\mathbb R\)-algebra with a nilpotent maximal ideal and residue field \(\mathbb R\). The simplest example is the dual-number algebra

\[
  A=\mathbb R[\varepsilon]/(\varepsilon^2).
\]

Its associated Weil functor \(T^A\) sends a smooth manifold \(M\) to its tangent bundle \(TM\). Other Weil algebras encode more elaborate finite-order infinitesimal information. A helpful intuition is that the algebra chooses an **infinitesimal probe shape**, and the functor applies that probe systematically to manifolds and smooth maps.

One reason this is mathematically satisfying is that these constructions are functorial, and compositions of Weil functors correspond, under the standard conditions, to tensor products of Weil algebras. They provide a genuine, rather than merely metaphorical, family of coherent transformations of differential-geometric structure.

What they do *not* do is supply a law of motion by themselves. A vector field is still extra data, a section \(v:M\to TM\). A finite-order probe is not the same thing as solving \(\dot x=v(x)\), and a Weil functor is not simply an ordinary exponent \(M^A\) in the category of smooth manifolds.

### Jet bundles: store exactly the derivatives that an equation mentions

Consider a scalar field \(u(t,x)\) satisfying the heat equation

\[
  u_t-\kappa u_{xx}=0.
\]

A second jet bundle records, at a point, the field value and derivatives up to order two: symbols such as \(u,u_t,u_x,u_{tt},u_{tx},u_{xx}\). The PDE becomes a constraint subspace of this jet bundle:

\[
  \mathcal E=\{\eta\in J^2(E):u_t(\eta)-\kappa u_{xx}(\eta)=0\}.
\]

This is an important conceptual move. The PDE is not initially a global update map taking one state to the next. It is a **condition on local derivative data**. A solution is a field whose jets lie in the equation locus and satisfy the compatibility conditions that make those derivative assignments arise from one underlying field.

The **Cartan/contact distribution** encodes those holonomicity constraints. Prolongation asks what additional differential consequences of the equation must hold at higher orders. A **diffiety** is one formalism for treating an infinitely prolonged differential equation with its induced differential structure.

This is why jet geometry belongs in a law-factorization toolkit. Changing a PDE changes an equation subspace and potentially its prolongations, symmetries, conservation laws, and solution families. Those changes can be studied without pretending that every law is an endomorphism acting on a fixed state space.

### Variational bicomplex: separate variation from differentiation along the base

For a Lagrangian field theory, one wants to manipulate differential forms on jet spaces while distinguishing derivatives along the independent variables (space/time) from variations of the fields. The **variational bicomplex** organizes these as horizontal and vertical differentials. It provides a systematic home for Euler–Lagrange expressions, boundary terms, conservation currents, and related identities.

This machinery is specialized, but its decomposition is precise: a field theory has variables, derivatives, equations, variations, and symmetries; keeping those roles apart makes statements such as Noether's theorem and integration by parts natural in a common calculus. It also helps expose when a proposed change of Lagrangian merely adds a boundary term and when it changes the equations of motion.

The limits matter. Jet geometry does not turn an arbitrary PDE into a well-posed initial-value problem. The equation subspace may be singular or formally incompatible; smooth formal jets need not extend to global solutions; boundary and initial conditions remain substantive. For systems in which only a low-dimensional ODE needs numerical integration, this geometric machinery may be unnecessary.

**Useful mental separation:** Weil functors vary the infinitesimal probe; jet bundles organize finite derivative data; Cartan geometry connects that data to genuine sections; the variational bicomplex organizes equations derived from variational principles. They are neighboring constructions, not synonyms.

---
## 12. Dirac structures and Tulczyjew geometry: keep dynamics implicit when the physics is implicit

State-update thinking also encourages solving equations for derivatives as early as possible. Physical networks often resist that: conservation constraints, power-conserving junctions, constitutive relations, and degenerate coordinates may define a relation between efforts and flows without choosing one as a function of the other.

### Dirac structures: separate interconnection from energy storage

A simple linear Dirac structure lives in a space \(V\oplus V^*\) of **flows** \(f\in V\) and **efforts** \(e\in V^*\). It is a maximally isotropic subspace for the symmetric pairing

\[
  \big\langle(f_1,e_1),(f_2,e_2)\big\rangle_+
  =e_1(f_2)+e_2(f_1).
\]

In particular, every \((f,e)\) in the Dirac structure satisfies \(e(f)=0\). With the usual port interpretation, that is a power-balance condition. The geometry says which flow/effort combinations are compatible with a lossless interconnection, before specifying the individual components' storage functions or dissipative laws.

A two-port example makes the idea less mysterious. Suppose ideal connection imposes equal effort \(e_1=e_2\) and balanced flows \(f_1+f_2=0\). Then

\[
  e_1 f_1+e_2 f_2=e_1(f_1+f_2)=0.
\]

The connection conserves power. A resistor or damper can subsequently be represented by a dissipative constitutive relation; an energy-storing device by a Hamiltonian. Keeping connection geometry, storage, and dissipation separate is precisely what makes port-Hamiltonian modeling compositional.

A Dirac structure is not a theorem that the complete physical system is solvable or stable. Constraint equations can have inconsistent initial conditions, nonunique motions, or singular points. Energy balance does not imply safe control, and a physically open system can exchange power with its environment rather than conserving its internal energy.

### Tulczyjew triples: Lagrangian and Hamiltonian presentations meet

Let \(Q\) be a configuration manifold. Classical mechanics often appears in two languages: a Lagrangian \(L:TQ\to\mathbb R\) using positions and velocities, and a Hamiltonian \(H:T^*Q\to\mathbb R\) using positions and momenta. The **Tulczyjew triple** relates the relevant tangent and cotangent bundles through canonical geometry, including maps of the form

\[
  TT^*Q\longrightarrow T^*TQ,
  \qquad TT^*Q\longrightarrow T^*T^*Q.
\]

This makes it possible to represent dynamics by geometric relations or Lagrangian submanifolds rather than insist that the dynamics first be solved as one privileged vector field. The decomposition is not “one equation translated into another notation”; it reveals how alternative mechanical presentations fit into common symplectic geometry.

For regular Lagrangians, the familiar Legendre transformation links the Lagrangian and Hamiltonian descriptions well. For singular Lagrangians, it need not be invertible, and constraint algorithms or implicit relations become necessary. Preserving that degeneracy is one of the reasons to use the geometric presentation rather than silently substituting a regular case.

**Where these techniques fit:** when the proposed variation concerns constitutive laws, energy functions, physical constraints, or interconnection geometry, Dirac/port-Hamiltonian and Tulczyjew machinery may preserve more of the physical meaning than a bare category of state updates. Courant algebroids and related generalized geometry become relevant when the variable Dirac structures, integrability, and bracket geometry themselves matter; they are not a default requirement for every constrained system.

---

## 13. Sheaves, groupoids, and derived solutions: what happens when local descriptions must become global?

Another attractive decomposition separates local data from global consistency. A spatially distributed physical theory may be easy to describe on small regions, yet a global solution can be obstructed by overlap conditions, topology, boundary values, or gauge identifications.

### Sheaves: restriction first, gluing second

A presheaf \(\mathcal F\) on a space assigns data \(\mathcal F(U)\) to each open region \(U\), with **restriction maps**

\[
  \rho_{UV}:\mathcal F(U)\to\mathcal F(V),\qquad V\subseteq U.
\]

For a sheaf, compatible local sections over an open cover glue uniquely to a global section on the covered region. Applied to differential equations, \(\mathcal F(U)\) might be the set of solutions on \(U\). A local solution restricts to a smaller domain, and locally agreeing solutions glue when the mathematical model satisfies the appropriate sheaf condition.

The direction of the restriction maps is essential. They are not forward-time evolution maps. Restricting a trajectory to a smaller time interval says which part of the trajectory is visible there; it does not compute its future extension. This is why a sheaf is useful for **local-to-global consistency**, not automatically for simulation or replanning.

A missing global section also does not mean that a stalk is empty or that the sheaf axiom failed. Local solutions may exist in every small neighborhood but no *globally compatible choice* may exist. A simple intuition comes from continuously choosing a square root around a circle: local choices can be made, but monodromy can prevent one continuous global choice. The obstruction is in extending and reconciling data, not in the sheaf having “holes” in its formal definition.

For dynamical systems, a **trajectory sheaf** over time intervals can record compatible segments. Replanning can then be expressed as an extension question: can a specified past section be extended into a future section satisfying the remaining constraints? The sheaf tells us what a compatible extension *means*. It does not provide a planning algorithm or guarantee one exists.

### Groupoids and stacks: sometimes equality is too strict

Suppose two local descriptions of a physical field differ by a gauge transformation. Requiring them to be literally equal on overlaps can be the wrong gluing rule. They may instead agree **up to a specified isomorphism**, and those isomorphisms must satisfy coherence on triple overlaps.

A groupoid records objects together with reversible identifications between them. A stack, in a common geometric setting, permits such groupoid-valued local data to satisfy descent. Its use is justified when the *ways* in which local objects are equivalent matter to the global assembly. Simply having heterogeneous agents or partial information does not create a stack problem.

The same warning applies to quotienting a solution space by symmetry. Taking only the set of equivalence classes can erase stabilizers and automorphisms. In gauge-sensitive problems those are real mathematical data, not decorative redundancy. A moduli groupoid or stack retains more of them.

### Derived solution spaces: failed transversality is information

Solving a collection of equations by taking an ordinary intersection may discard multiplicities and obstruction information. Consider the elementary equation \(x^2=0\) over \(\mathbb R\). Its ordinary solution set is just \(\{0\}\), yet its linearization at zero is the zero map: first-order perturbation theory sees a degeneracy absent from the bare set of solutions. Derived intersections and derived critical loci are ways of recording such nontransverse or higher-order structure.

This is relevant to *varying laws*: a generic parameter can split or eliminate solutions, and a singular parameter can produce new infinitesimal freedoms or obstructions. A bare list of solution points may not predict what happens under perturbation. Derived geometry can retain the missing information, but it brings substantial machinery and does not itself ensure analytic existence of solutions to physical field equations.

The unifying idea here is that **global consistency, equivalence, and deformation are three different issues**. Sheaves address gluing compatible local sections; stacks retain coherent isomorphisms between local objects; derived structures retain higher-order intersection and deformation information. They are complementary only when those distinct phenomena are actually present.

---

## 14. Lenses, open games, and interaction semantics: other ways a component can face its environment

The open-component problem is not limited to state evolution under physical laws. Some systems exchange information or objectives in both directions, or consist of agents reacting strategically to one another. Several less conventional constructions make different parts of that interaction primitive.

### Lenses and optics: a forward channel with a backward response

A simple lens has a forward observation \(\mathrm{get}:S\to A\) and a backward update \(\mathrm{put}:S\times A\to S\), with additional laws for well-behaved lenses. More general optics use other types and residuals. The point is to separate **what is exposed forward** from **what can be sent back as an update or request**, while retaining a discipline for their composition.

This is useful for editable views, bidirectional transformations, some learning architectures, and cybernetic systems. It is not automatically a control law: the backward channel may represent a requested update, a gradient, or a continuation, each requiring its own semantics. Calling all of those “feedback” would conceal important differences.

### Open games: forward play, backward consequences, equilibrium selection

In compositional game theory, an open game supplies strategic structure associated with an interface—often described in terms of play, coplay or coutility, strategy sets, and an equilibrium-selection rule. Games compose through their interfaces, making it possible to build larger strategic interactions without rebuilding the entire equilibrium condition from scratch.

This cut is useful when the component's behavior depends on preferences and strategic responses, not merely exogenous stochastic uncertainty. But an open game is not simply a morphism *equal to* a strategy profile, and its failures are not generically “no Nash equilibrium.” Every finite normal-form game with nonempty finite strategy sets and real payoffs has a mixed-strategy equilibrium, while pure equilibria can fail to exist. Which equilibrium notion a component exposes is a modeling choice.

### Dialectica and geometry of interaction

Dialectica-style constructions separate witness-producing and counter-witness or challenge structure. They become attractive when a system is understood through **a proposed move and a response that tests or refutes it**—a perspective that can fit adversarial verification and robust contracts.

Geometry-of-interaction approaches give a different emphasis to how processes execute through interaction and feedback. They can be valuable when execution traces, token flows, or repeated interaction are more fundamental than a global transition function. Again, there is no automatic passage from a generic categorical trace to a physically faithful dynamic semantics.

These techniques belong in the wider toolkit because they suggest **different notions of boundary**, not because every dynamical system secretly is a lens or a game. A physical plant, an editable view, a strategic agent, and a proof/refutation protocol may all be compositional, but their interaction rules are not interchangeable.

---

## 15. Assemble the pieces: a boundary-first architecture

The various decompositions now point toward a more precise design than a universal “category of dynamical systems.” Start by declaring *which components may interact and what an external user of a component may observe or demand*. Only then choose internal representation families and mathematical tools to implement that contract.

Let \(B\) denote a boundary type. It can include signals and commands, but also timing, failure reports, information available to a controller, permitted interactions, and any resource or physical compatibility data required by the intended application.

For that boundary, define two different spaces of descriptions:

\[
  \mathsf{Impl}(B):\text{ internal implementations at }B,
\]

\[
  \mathsf{Beh}(B):\text{ boundary behaviors relevant to its consumers}.
\]

There is a semantics map or interpretation

\[
  \beta_B:\mathsf{Impl}(B)\longrightarrow\mathsf{Beh}(B).
\]

Different implementations can have different state spaces, law representations, or solver machinery. The goal is **not** to make those internal objects identical. It is to make their exposed behavior comparable at the declared boundary.

Now suppose a wiring pattern \(w\) connects components with boundaries \(B_1,\ldots,B_n\) to produce a boundary \(B\). Ideally assembly exists both on implementations and on behaviors, with a compatibility law of the form

\[
\beta_B\!\bigl(\mathsf{Asm}^{\mathrm{Impl}}_w(C_1,\ldots,C_n)\bigr)
\;\cong\;
\mathsf{Asm}^{\mathrm{Beh}}_w\!\bigl(\beta_{B_1}(C_1),\ldots,\beta_{B_n}(C_n)\bigr).
\]

The isomorphism is schematic: a particular model may call for literal equality, refinement/inclusion, or a sound abstraction rather than an isomorphism. The requirement is that **interpreting an assembled system agrees, in the specified sense, with assembling the interpretations of its parts**. If this fails, the boundary semantics is not compositional under that wiring.

This is the actual theorem-shaped target behind the earlier intuition about decomposition. No combination of familiar category names proves it by inspection.

### What must the boundary semantics preserve?

There is no fixed answer independent of the intended user. For a position monitor, observable position traces may be enough. For a safety controller, the semantics may need to preserve must-enabled commands and fault behavior. For a scheduler, deadlines and worst-case execution times may be essential. For a feedback network, causal structure or a particular trace interpretation may be required.

A strong notion of substitutability can be expressed by quantifying over allowed external contexts \(K\): two components are equivalent if their observable behaviors agree in every permitted \(K\). A weaker, asymmetric refinement may suffice for a contract. For example, a replacement accepting *more* commands while preserving the old guarantees can be acceptable; demanding exactly equal definedness domains would unnecessarily reject it. Conversely, a replacement that agrees on successful outputs but sometimes diverges is unacceptable when termination is part of the contract.

Thus three different goals should not be collapsed:

**Exploratory variation:** a law or representation changes, and its consequences for the boundary are recalculated. No boundary preservation is promised.

**Verified replacement:** an implementation changes while a specified class of boundary contracts is preserved or refined.

**Abstraction:** some internal distinctions are deliberately forgotten while retaining sufficient information to answer selected external questions.

The difference is practical. “Vary the internals freely” makes sense for exploration only if the consequences are allowed to change. “Swap the component safely” requires a preservation theorem. “Use the smallest boundary model” requires proving that the omitted distinctions are irrelevant to every designated consumer.

### Where the mathematical tools enter—and where they do not

At this stage the techniques have clear, conditional jobs:

| Design need | Useful starting mechanism |
|---|---|
| Repeated external operators with coherent composition | Actegory |
| Families of systems varying over theories or parameters | Indexed category / fibration |
| Syntax of laws and models satisfying them | Institution / doctrine |
| Explicit state with an abstract step/observation form | Coalgebra |
| Laws as constraints on complete trajectories | Behavioral systems theory |
| Typed network assembly | Wiring diagrams, operads, cospans, appropriate monoidal/double categories |
| Partial deterministic process composition | Restriction category / partial map category |
| Multivalued constraints and converse reasoning | Relations, allegories |
| Nondeterministic, stochastic, or other computational effects | Appropriate Kleisli/effect semantics |
| Knowledge and enabledness under hidden state | Observation/information-state and modal semantics |
| Independent events, branching, and causal concurrency | Event structures |
| Smoothness on non-manifold carriers | Diffeological / Frölicher spaces |
| Differential constraints and variational laws | Jets, Cartan geometry, variational bicomplex |
| Energy-conserving physical interconnection | Dirac / port-Hamiltonian structures |
| Local consistency, gauge identifications, deformation | Sheaves, stacks, derived solutions |
| Strategic or bidirectional interaction | Open games, lenses, dialectica/interaction semantics |

This table is not a menu of mutually exclusive components to stack automatically. Some tools work at different levels, and some have incompatible assumptions until an interpretation has been supplied. The selection test is always: *what question will this tool make answerable or what obligation will its laws discharge?*

---
## 16. One complete pass: from a local update to a system-level control claim

The actuator example can now be run through the architecture without invoking a large category-theoretic superstructure. This is useful because it reveals exactly which extra structure each desired inference requires.

### First, choose the internal process semantics

Let \(S=\mathbb Z\times\{0,\tfrac12,1,\tfrac32,2\}\), a toy state space with discrete temperature levels. Let commands be \(u\in\{0,1\}\). On states for which the result remains in \(S\), define

\[
 a_u(x,\theta)=(x+u,\theta+u^2),
 \quad \text{provided}\quad \theta+u^2\le2.
\]

For \(u=1\), the enabled temperatures are \(0,\tfrac12,1\). For \(u=0\), the position and temperature stay fixed. The restriction \(\bar a_1\) is the partial identity on states with \(\theta\le1\).

The successful two-command behavior \(a_1\circ a_1\) is defined only at \(\theta=0\), because the temperature increases by one each time. That result is a compositional *definedness* fact. It does not yet say that two moves are physically safe, desired, or externally permissible.

### Second, connect a downstream constraint

Suppose a downstream receiving component accepts positions at most 1. Model its one-step admissibility as a partial observation/handshake operation \(g\) defined only when the received position is \(x\le1\). If the initial shaft position is \(x=1\), command \(u=1\) may be internally enabled and produce \(x'=2\), but the composite handshake \(g\circ a_1\) is undefined.

The local actuator domain did not change. The composite domain did because the actual output failed a downstream precondition. This is why calculating global definedness requires behavior as well as the local restriction idempotents.

A different system contract might prohibit even *starting* a command whose eventual receiver will reject it. That contract needs a pre-execution test or a planning proof, not merely the fact that the composite partial function is undefined after both stages have been interpreted.

### Third, specify what the controller can observe

Let the readout be \(r(x,\theta)=x\). At position \(x=0\), hidden states \((0,0)\) and \((0,2)\) are indistinguishable from one instantaneous reading, but they disagree about whether \(u=1\) is enabled. The internal guard does not descend to an exact position-only guard.

A controller whose current information set is

\[
  B_h=\{(0,0),(0,2)\}
\]

can infer that a move **might** be enabled, not that it is guaranteed enabled. If the action is tried, the actual API semantics becomes decisive:

- If a disallowed command is **undefined**, the mathematical model gives no reported outcome.
- If the device **returns a thermal error**, the response may reveal something about hidden temperature.
- If it **blocks without response**, the controller has a different temporal/epistemic problem.
- If it **moves partway and then faults**, recovery must account for the altered physical state.

The choice between these is not a stylistic choice about modeling exceptions. It changes the subsequent information state and which plans remain available.

### Fourth, vary a law without pretending to preserve the whole contract

Replace the temperature increment by \(\tfrac12u^2\), while keeping the same position increment and same temperature limit. This new actuator accepts command \(u=1\) at \(\theta=\tfrac32\), where the original rejects it. For the same hidden state and first move, its position output is unchanged. But its temperature trajectory is not unchanged, so its set of future enabled commands can differ.

That variation is perfectly legitimate for exploring physical models. It is **not automatically** a drop-in substitution for a component whose boundary contract includes fault reporting or future affordances. A contract restricted to one-step successful position output under old admissible inputs may be refined by the new implementation; a contract describing all future error traces needs a separate comparison.

Conversely, adding a temperature sensor would change the boundary information without changing the actuator's heating dynamics. The controller could then distinguish some cases previously merged. That is an **observation variation**, not a law variation.

### Fifth, ask what replanning actually means

Suppose the controller needs to reach position 2 but has only command \(u=1\) and the stay-put command \(u=0\). With initial \(x=0,\theta=1\), the actuator can move once to \((1,2)\) but cannot perform the second move. Under this model, repeatedly choosing \(u=0\) does not cool the device; the target is unreachable. No categorical composition operation invents a feasible continuation.

If a cooling command is added, such as

\[
  c(x,\theta)=(x,\max(0,\theta-1)),
\]

then new continuations may exist. Whether the controller can choose one safely still depends on its knowledge of temperature, the command's enabledness, and what the downstream receiver accepts. Replanning is now an explicit search or synthesis problem in a changed action system, not a lower element in a lattice or a gluing operation that somehow performs optimization.

If the task has a deadline, elapsed time and cooling duration must appear in the state or contract. If failure is irreversible, execution prefixes must be retained. If heating is random, a stochastic safety criterion must be chosen. Each added feature changes the questions and the required data in a specific way.

### What this example establishes

A single system supports several descriptions—partial function, observational quotient, contract, connected component, and planning problem—but these descriptions live at different levels. Their relationship must be constructed. The example also demonstrates why preserving only the position readout, or only the set of individually enabled commands, is inadequate for some controllers. The omitted temperature is relevant precisely because later steps consume it.

---

## 17. A practical way to choose a decomposition

Rather than ask which abstraction is the most advanced, start with the **operation that must work** and work backward to the distinctions it requires.

For example, if the immediate task is to compare two possible force laws on the same carrier, a parameter-indexed dynamical model may be sufficient. If the task is to wire the same components in different physical networks, the crucial representation is the interface and connection semantics. If it is to show that a controller can issue a command based only on a sensor stream, the central issue is information and strategy—not the elegance of the internal state category.

The selection can be framed as a sequence of questions:

**What is the object of variation?** A numerical parameter, a differential equation, a constraint, a symmetry, a port configuration, an observation map, or the very kind of process (deterministic versus stochastic)? Different answers suggest different model families. Do not replace them all by an untyped “law.”

**What is the external consumer allowed to do?** Merely read outputs, issue commands, reconnect ports, create feedback loops, infer hidden state, or require temporal guarantees? A boundary adequate for one consumer may be too coarse for another.

**What does failure mean at that interface?** Undefined update, explicit error value, numerical nonconvergence, constraint violation, inability to extend a partial trajectory, or failure of a planning specification? Model the needed distinction rather than naming all of them “exceptions.”

**What must composition preserve?** Legal wiring, successful execution, all possible outcomes, time, resource use, safety, knowledge, or strategic ability? The relevant proof obligation is often stronger than the existence of a composite arrow.

**Can the proposed abstraction actually be computed or observed?** The existence of a predicate or restriction idempotent does not make it a decidable API guard. The existence of a feasible continuation does not yield a plan. A sheaf gluing axiom does not find local sections.

**Which distinctions can be safely forgotten?** This is the key question before quotienting. A coarse model is useful only relative to the observations, decisions, contexts, and guarantees it preserves. If an uncertain distinction could change a controller's action or a verifier's judgment, retaining it in reserve is safer than declaring it irrelevant.

### A useful small target before attempting a universal architecture

A concrete construction problem would be:

1. Choose a class of deterministic, discrete-time open components with explicit hidden state, partial updates, and typed input/output ports.
2. Give serial and parallel wiring an unambiguous operational semantics; defer instantaneous feedback until its meaning is fixed.
3. Define boundary behavior as a specified set of finite input/output/error traces, together with whatever enabledness information the intended controller can use.
4. Prove that the boundary interpretation is compositional for the chosen wiring operations—or exhibit where it fails.
5. Define a refinement relation and check that it is preserved by every allowed wiring context.
6. Only then test whether restriction structure, indexed variation of laws, nondeterminism, feedback, or modal controller guarantees can be added without changing the previous meaning silently.

This order has a practical advantage. A theorem can fail for an informative reason: hidden state may be insufficiently summarized; a fault result may be suppressed; a feedback loop may require causality data; or a chosen abstraction may not preserve must-enabled commands. Each failure identifies information that the interface must carry or an operation that must be restricted.

Trying to begin instead with an all-purpose stack of actegories, fibrations, sheaves, restrictions, optics, and trace often reverses the dependency. The resulting architecture can have beautiful components but no verified claim about what actual composed systems do.

---

## Closing perspective

The appealing feature of actegories was the possibility of cleanly separating operators from the systems they transform. That appeal survives the broader exploration, but the most useful lesson is more general: **decomposition works when the interface between the pieces is semantically precise enough to support the operations that will later consume it**.

Coalgebras put state and behavior type on opposite sides of a seam. Behavioral systems theory removes the presumption that an internal state description comes first. Institutions separate law statements from models; fibrations organize model families over contexts. Wiring calculi isolate assembly. Restriction categories capture compositional partiality. Modal and epistemic semantics expose the gap between an internally enabled action and one a controller can knowingly perform. Event structures preserve concurrency without manufacturing an order. Jets and Dirac structures retain forms of physical constraint that are distorted by premature conversion to state updates. Sheaves and stacks preserve kinds of local-to-global information that ordinary global state descriptions often discard.

None is a universal decomposition. Nor do they form a refinement ladder. Their power comes from keeping *different questions different* long enough to decide which interfaces and laws are needed.

The unresolved, worthwhile problem is therefore not “find the most expressive mathematical object for a complicated environment.” It is to construct a compositional boundary semantics for heterogeneous components, with explicit classes of permissible variation and replacement, and with proofs that the distinctions relevant to observation, control, failure, and verification survive assembly. That problem is narrower than a universal theory of dynamics, but it is also much more testable.
