# Corrected notes on the decomposition of dynamical and open systems

*An expanded, modular synthesis of the supplied AI conversation.*

# Notebook index

**Source:** the uploaded AI conversation `Pasted text(20261027-151133).txt` (chat line references run L1–L2737). **Purpose:** turn an exploratory dialogue into usable notes, not preserve its chronology, assistant confidence, or original taxonomy. **Coverage:** 23 independent notes; law operators, constraints, behavioral modeling, internal/boundary composition, modalities, failure, generalized smoothness, concurrency, geometric mechanics, and a concrete development path.

## Start here by interest

| Problem / consumer | Relevant notes | Non-negotiable caveat |
|---|---|---|
| Define the system decomposition and interfaces | [01](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/01-problem-and-semantic-interface.md), [20](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/20-architecture-and-proof-obligations.md) | No unconditional theorem that local validity implies global validity |
| Preserve semantics under abstraction or replacement | [02](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/02-preservation-and-substitutability.md), [21](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/21-small-worked-example.md) | Equality of I/O types is insufficient; which contexts observe behavior? |
| Factor laws out of system models | [03](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/03-types-of-physical-law.md), [04](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/04-actegories.md), [06](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/06-indexing-institutions-doctrines.md) | A family of laws is not automatically a monoidal action |
| Avoid a state-space bias | [05](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/05-coalgebra-and-behavior.md), [10](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/10-relations-allegories-and-effects.md) | Behavior as a relation may lose implementation and causal information |
| Compose open systems | [07](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/07-wiring-and-open-systems.md), [11](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/11-feedback-and-trace.md) | Feedback requires its own semantic rules and often well-posedness |
| Express partial operations and observer-visible capabilities | [08](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/08-restriction-categories.md), [09](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/09-observation-and-modal-affordances.md) | Definedness is neither decidability nor knowledge nor safety |
| Local/global consistency and solution moduli | [12](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/12-sheaves-and-stacks.md), [17](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/17-gauge-and-derived-solution-spaces.md) | Gluing and derived data do not synthesize trajectories |
| Model non-global time and concurrency | [13](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/13-events-concurrency-causality.md) | Causal order does not supply metric time or evolution |
| Model non-manifold states or differential laws | [14](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/14-diffeology-and-frolicher.md), [15](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/15-weil-jets-and-pde-geometry.md) | Smoothness/infinitesimal data does not imply well-posed dynamics |
| Model energy/implicit physical laws | [16](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/16-dirac-and-implicit-physical-systems.md) | Energy balance is not global solvability, stability, or reversibility |
| Model bidirectional information/incentives | [18](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/18-lenses-games-and-interactions.md) | A backward channel does not automatically mean controller, gradient, or equilibrium |
| Model exceptions, reachability, and replanning | [19](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/19-exceptions-and-replanning.md) | Composition is not plan synthesis |
| Decide what to test/build next | [22](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/22-probes-and-unresolved-questions.md), [23](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/23-other-techniques-in-reserve.md) | A concept's existence is not an application theorem |

## Recommended reading sequences

**Shortest path to the original research idea:** 01 → 02 → 07 → 08 → 09 → 20 → 21 → 22. This gives the typed boundary problem and the main obstructions before introducing specialized machinery.

**Law/model factorization:** 03 → 04 → 06 → 05 → 15 → 16. This retains the distinction between law as operator, equation, index, generator, and physical constraint.

**Less conventional techniques:** 10 → 11 → 13 → 14 → 15 → 16 → 17 → 18 → 23. Each note states both a genuine mathematical payoff and what the apparatus does *not* automatically imply.

## Standalone notes

<!-- BEGIN MANIFEST -->
- [01 · What is actually being decomposed?](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/01-problem-and-semantic-interface.md)
- [02 · Preservation, observational equivalence, and the cost of quotienting](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/02-preservation-and-substitutability.md)
- [03 · “Physical law” is a role-indexed family, not one operator type](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/03-types-of-physical-law.md)
- [04 · Actegories separate operator algebra from carrier semantics](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/04-actegories.md)
- [05 · Coalgebra versus behavior-first system modeling](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/05-coalgebra-and-behavior.md)
- [06 · Fibrations, institutions, and doctrines: three different law/parameter interfaces](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/06-indexing-institutions-doctrines.md)
- [07 · Wiring formalisms: interfaces, assembly, and hidden state](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/07-wiring-and-open-systems.md)
- [08 · Restriction categories: the algebra of *definedness*](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/08-restriction-categories.md)
- [09 · From internal actions to observable capabilities](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/09-observation-and-modal-affordances.md)
- [10 · Relation-first dynamics, allegories, Kleisli categories, and effects](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/10-relations-allegories-and-effects.md)
- [11 · Feedback is an operation with its own existence and coherence obligations](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/11-feedback-and-trace.md)
- [12 · Local-to-global behavior: presheaves, sheaves, and stacks](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/12-sheaves-and-stacks.md)
- [13 · Events and causal structure instead of one global state clock](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/13-events-concurrency-causality.md)
- [14 · Diffeological and Frölicher spaces: smoothness without manifold charts](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/14-diffeology-and-frolicher.md)
- [15 · Weil functors, jets, Cartan distributions, and the variational bicomplex](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/15-weil-jets-and-pde-geometry.md)
- [16 · Dirac structures and Tulczyjew triples: constraints, energy, and dynamics](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/16-dirac-and-implicit-physical-systems.md)
- [17 · Groupoids, stacks, and derived solution spaces: do not erase witnesses too early](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/17-gauge-and-derived-solution-spaces.md)
- [18 · Lenses, open games, and interaction semantics](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/18-lenses-games-and-interactions.md)
- [19 · Exceptions and replanning: distinguish the event, the judgment, and the obstruction](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/19-exceptions-and-replanning.md)
- [20 · A typed architecture for heterogeneous open components](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/20-architecture-and-proof-obligations.md)
- [21 · Worked finite example: what survives the boundary?](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/21-small-worked-example.md)
- [22 · Discriminating probes and unresolved research questions](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/22-probes-and-unresolved-questions.md)
- [23 · Other decomposition techniques in reserve](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/notes/23-other-techniques-in-reserve.md)
<!-- END MANIFEST -->

## Three warnings that should survive future compression

1. An internal category of executable partial transitions and a category of **open components** are generally different levels; an internal restriction idempotent does not automatically determine an observable boundary restriction.
2. A categorical operation can guarantee correct *composition* of meanings without furnishing a feasibility decision algorithm, solver, controller, or optimal policy.
3. Any claim of minimal, universal, or “freely varying” system factorization is conditional on declared interfaces and the questions that need to remain answerable after assembly.

The notebook also includes a [finite verification record](../exposition/corrected-system-decomposition-notebook/decomposition_notebook/CHECKS.md). It complements—but does not supersede—the earlier, more forensic 40-claim audit, included as a separate appendix in the ZIP. This main notebook is intended to be reusable as individual knowledge notes.

---

# The 23 notes


---

## 01 — What is actually being decomposed?

**Origin:** chat L1435–1441, L1958–1960, L1988–2013, L2279–2306, L2543–2631. **Status:** corrected synthesis; the formal contract below is a proposal.

## The motivating problem

The target is **not** a classifier that maps an environment property to a mathematical object. It is an open-system architecture in which subsystems can have *different internal mathematical representations*, while their external interaction and the guarantees that survive assembly are explicit.

The key question is: *what may an environment, controller, verifier, or other subsystem infer and do through the boundary of a component?* A state-space dimension, input/output signature, or collection of formulas alone cannot answer it.

A component specification can be organized as

\[
C=(B,S,H,I,U,Y,\delta,r,\mathsf{Fault},\mathsf{Spec}),
\]

where **B** is an interface type (possibly carrying time and protocol structure); **S** an internal state carrier; **H** admissible histories; **I** initial-state assumptions; **U** commands/inputs; **Y** externally visible results; **δ** transitions (a map, relation, kernel, or continuous dynamics); **r** observation/readout; **Fault** explicitly observable or modeled failures; and **Spec** designated safety, liveness, resource, and performance requirements. This is a *checklist*, not a universal mathematical definition: types and some fields depend on the domain.

## Three different tasks

1. **Decomposition:** break a system into open components and give compatible assembly operators. The pieces need not retain all details of the original presentation, but collectively must reconstruct the selected behaviors or guarantees.
2. **Variation:** change a component's law, observation, state, model, or internal decomposition. Its boundary contract may change; identify and revalidate affected consumers.
3. **Substitution:** replace a component without violating a *declared* external contract in *specified* contexts. Contextual equivalence or refinement is required, not identity of implementation or of all restrictions.

The original chat drifted between (2) and (3). “Vary laws freely” is appropriate only in the sense of *permitting well-typed changes* and propagating their effects. “Preserve the whole boundary semantics” defines a much narrower substitution problem.

## Separate semantic facets before choosing theory

| Facet | Example question | What it cannot be replaced by |
|---|---|---|
| Carrier | What states/configurations exist? | Observation classes |
| Evolution | What successor behavior is possible? | An ordering on states |
| Information | What can be inferred from available measurements? | Actual state truth |
| Enabledness | Where is a particular command defined? | Safety or a computable guard |
| Outcome/fault | Does failure block, return error, crash, or change state? | Undefinedness alone |
| Specification | What is required, allowed, forbidden, optimized? | A mathematical domain without a task law |
| Assembly | Which compatible components can be connected? | A proof that their guarantees compose |

These are **interacting interfaces**, not independently selectable tensor factors. A consumer of composition, verification, control, or audit can force finer distinctions than the initial model designer anticipated.

## Criterion of success

A representation is adequate if every designated consumer has a sound way to answer its questions using the boundary data and the assembly rules. A reduction is justified only relative to those consumers. If two hidden states are merged but admit different actions, an observation-only controller cannot automatically inherit a state-aware plan.

**Failure condition:** treating a typed connection, a valid local transition, and a global guarantee as equivalent claims. They are three separate obligations.

**Related notes:** Note 02, Note 07, Note 20.

---

## 02 — Preservation, observational equivalence, and the cost of quotienting

**Origin:** the user's open-system target at chat L1958–1960, plus the original claims about boundary contracts at L2543–2589. **Status:** added formal design note; not a theorem asserted by the source.

## Define the consumer before defining equivalence

Let \(\mathcal K\) be the class of external contexts that may use a component, and \(\mathrm{Obs}\) the allowed external observations (including error reports, timing, termination, and resource use **if those matter**). A stringent notion of contextual equivalence is

\[
C\approx_{\mathcal K,\mathrm{Obs}}D
\quad\Longleftrightarrow\quad
\forall K\in\mathcal K:\ \mathrm{Obs}(K[C])=\mathrm{Obs}(K[D]).
\]

This cannot be evaluated until \(K[C]\) is given a composition semantics and the observable behaviors are defined. For refinement, replace equality by an explicitly oriented preorder. If a specification guarantees only absence of bad *finite traces*, trace inclusion may support refinement; it does **not** alone preserve termination, liveness, or progress under all contexts.

### Two kernels that must not be conflated

**Representational quotient:** an abstraction \(\alpha:S\to\widehat S\) identifies internal states. It may preserve a predicate yet fail to preserve enabledness, future behavior, or policy information. The abstract transition must be defined and checked separately, for example through simulation or bisimulation conditions.

**Observational quotient:** two implementations are indistinguishable for the chosen consumers and contexts. It can be coarser than state equivalence or stricter than equality of one-step input/output relations when feedback and failure are observable.

The relevant law is the stakeholder's verification/control contract, not an unconditional preference for the smallest state space. The gain from coarse models is reduced analysis cost; the hazard is deletion of a distinction that matters to a downstream consumer.

## Counterexample: a hidden cut that changes executable action

Let \(S=\{s_0,s_1\}\), with the same readout \(r(s_0)=r(s_1)=o\). A command \(a\) is enabled only in \(s_0\). Merging the two states is legitimate for the instantaneous readout, but not for a deterministic Boolean `enabled?(o)` or guaranteed safe execution. The quotient requires a *may/must* distinction or a belief state.

## Contract refinement is asymmetric

Suppose a server originally accepts commands in \(D\subseteq U\), and a replacement accepts \(D'\supseteq D\) with equivalent results for old commands. For a client restricted to \(D\), the enlarged domain can be a valid improvement. Requiring equality of restriction domains would reject it unnecessarily. Conversely, a replacement can preserve all successful output values but introduce divergence, violating a termination guarantee.

**Ratchet:** test two candidate implementations in every *allowed* interconnection—not in every imaginable universe. If the contexts include feedback, include closed loops; if they include clocks, include deadlines; if they include control, include the permissible observation histories and strategy classes.

**Related notes:** Note 09, Note 11, Note 20.

---

## 03 — “Physical law” is a role-indexed family, not one operator type

**Origin:** chat L444–514 and L465–500. **Status:** source-derived taxonomy with corrections.

The early actegory discussion correctly rejects a universal category of *laws*. A law may describe **evolution, admissibility, selection, symmetry, constitutive response, or interconnection**; these have different types. Even the same written equation may be used in several roles, depending on what variables are taken as inputs, states, controls, or observations.

| Law role | Minimal mathematical shape | What must be supplied to get behavior |
|---|---|---|
| Evolution map | \(f:S\to S\), or \(T:S\times U\to S\) | Time convention, enabled actions, solution or iteration |
| Infinitesimal generator | \(v:S\to TS\) | Existence/uniqueness or differential-inclusion solution semantics |
| Constraint | \(R\subseteq X\times Y\) or equation \(F(x,y)=0\) | Which variables are solved for, feasibility, possible multiplicity |
| Variational principle | Functional \(\mathcal A:\mathrm{Paths}\to\mathbb R\) | Variation class, boundary data, extremality/stationarity rule |
| Symmetry | Action plus invariance/equivariance judgment | Which object is transformed and which quantities are invariant |
| Conservation | \(I:S\to V\), with \(I(\phi_t(s))=I(s)\) | Existence of trajectories; proof of invariance |
| Constitutive | Response relation between efforts, flows, strains, etc. | Coupling to balance laws and boundary conditions |
| Wiring/coupling | Typed composition of ports and constraints | Existence and well-posedness of composite system |
| Measurement | Observation map/kernel and sensor protocol | Noise, calibration, information structure |

The table classifies **mathematical role**, not the scientific provenance or ultimate validity of a theory.

## Why an actegory is conditional here

An actegory requires not only a family of operations but a monoidal algebra of those operations, functorial action on system objects *and arrows*, and coherent interaction. Vector fields do not automatically furnish it: a collection of fields parameterizes potential dynamics, while their flows need not commute, exist globally, or respect an imagined tensor product of laws.

A law such as \(F(x,y)=0\) is often better treated relationally. If solving for \(y\) is unique and well-posed, it *may* induce a map. That step is not invertible: it loses information about solution multiplicity or the variables no longer exposed. A Hamiltonian requires a Poisson/symplectic structure to generate dynamics, and a Lagrangian requires an admissible variation/geometry, not just a law-object acting on arbitrary systems.

## A useful comparative experiment

Fix one circuit network topology and compare three variants: (i) change only component parameters, (ii) replace a constitutive relation by a multivalued one, (iii) change the interconnection pattern. The first is often an indexed parameter change; the second can alter the type of process semantics; the third changes wiring. Requiring all three to be “the same law action” obscures the actual changes and their verification costs.

**Related notes:** Note 04, Note 06, Note 16.

---

## 04 — Actegories separate operator algebra from carrier semantics

**Origin:** chat L2–382, L386–440, L518–588, L2441–2488. **Status:** definition retained; application claims corrected.

## Mathematical core

A left action of a monoidal category \((\mathcal V,\otimes,I)\) on a category \(\mathcal C\) is a functor

\[
\odot:\mathcal V\times\mathcal C\longrightarrow\mathcal C
\]

with coherent natural isomorphisms \((v\otimes w)\odot c\cong v\odot(w\odot c)\) and \(I\odot c\cong c\). Equivalent data can be expressed as a **strong monoidal** functor \(\mathcal V\to\operatorname{End}(\mathcal C)\), where endofunctors compose. The functor acts on *arrows*, too. An actegory is a categorical action; it is only analogous to an ordinary module unless additive/distributive structures are also supplied. See [Capucci–Gavranović](https://arxiv.org/abs/2203.16351).

### Three common look-alikes

- A time **monoid acting on one state object**, \(\phi_{t+s}=\phi_t\phi_s\), is not by itself an actegory on a category of dynamical systems.
- A **parameterized family of laws** \(f_\lambda\) need not have any algebra of parameter composition.
- A **graded monad** is ordinarily described using lax monoidal structure; its grade-composition maps need not be isomorphisms. It is not automatically an actegory.

## Multiple actions are not independent by default

Actions of \(\mathcal V\) and \(\mathcal W\) on the same \(\mathcal C\) may commute up to coherent interchange, interact through distributive or semidirect-type data, or fail to admit a joint action. Interchange is *extra structure*. A bare notation such as \(\mathcal V,\mathcal W\curvearrowright\mathcal C\) does not construct it.

**Witness.** On \(\mathbb R^2\), take \(V=\partial_x\) and \(W=x\partial_y\). Their flows are \(\Phi_t^V(x,y)=(x+t,y)\) and \(\Phi_s^W(x,y)=(x,y+sx)\). Applying them in opposite orders changes \(y\) by \(st\). “Independent operator kind” does not imply commuting dynamics.

## Restriction-preserving actions cannot freely alter definedness

For a restriction functor \(F\), \(F(\bar f)=\overline{Ff}\). If \(f\) is total, then

\[
\overline{Ff}=F(\bar f)=F(1)=1.
\]

Therefore a restriction-preserving functor preserves total maps. On a fixed carrier, this mechanism cannot create new partiality from a total arrow. If changing laws is intended to make previously valid inputs invalid, the semantics must allow such variation explicitly through another typed construction. This is an obstruction to a proposal in chat L2441–2488, not an objection to actegories themselves.

## Selection criterion

Use an actegory when the operator family *already has a coherent composition algebra* and its members transform both systems and relevant system maps. Do not choose it solely because operators and states can be described separately. Lifting adjunctions, monads, constraints, or contracts requires additional compatibility arguments.

**Related notes:** Note 03, Note 06, Note 08.

---

## 05 — Coalgebra versus behavior-first system modeling

**Origin:** chat L665–721 and L918–958. **Status:** retained, sharpened, and expanded.

These offer two different cuts through “state plus dynamics.” They should be kept as alternatives, not merged into a supposed general ladder.

## Coalgebra: explicit state with an abstract behavior signature

An \(F\)-coalgebra is \(c:X\to F(X)\), for a specified endofunctor \(F\). The functor fixes the *one-step behavioral shape*; the coalgebra map specifies a particular system. Examples include \(F(X)=Y\times X\) for output streams and \(F(X)=(Y\times X)^U\) for a total deterministic input-driven Mealy machine. Powerset-like and distribution functors model selected forms of branching or randomness under their respective categories and size/measure restrictions.

Coalgebra exposes tools such as behavioral equivalence and bisimulation when suitable final coalgebras or relation liftings exist. It does not supply observation semantics, control objectives, or a wiring calculus automatically; also, different choices of \(F\) are materially different model classes.

## Willems-style behavioral systems: do not privilege input/output or state

A behavior-first system is a set of admissible trajectories

\[
\mathcal B\subseteq W^T.
\]

Here \(W\) is a signal-value space and \(T\) a time or indexing set. Differential equations, algebraic relations, and network constraints *select* the behavior. Inputs and outputs may be designated later rather than being intrinsic. This is the essential antidote to automatically converting every law to \(x_{t+1}=f(x_t,u_t)\). [Willems, behavioral approach](https://citeseerx.ist.psu.edu/document?doi=12e43968c77466cfbd4720f2651220a9d7a5e365&repid=rep1&type=pdf).

### Composition by constraints and hiding

For two behaviors sharing a signal \(z\), the composed behavior can be written

\[
\mathcal B_{AB}=\{(x,z,y): (x,z)\in\mathcal B_A,\ (z,y)\in\mathcal B_B\}.
\]

If \(z\) is internal, hide it through projection:

\[
\mathcal B_{\mathrm{ext}}=\{(x,y):\exists z\ (x,z,y)\in\mathcal B_{AB}\}.
\]

This is a powerful mathematical decomposition: interconnection is constraint intersection/join, and encapsulation is existential elimination. But existential hiding can lose uniqueness, causality, diagnostic information, or the feasibility of online implementation. A behavior as a set of traces also does not by itself identify controllable versus uncontrollable coordinates.

## Selection test

If the scientific law is primarily an equation constraining *whole trajectories* (DAE/PDE, reciprocal or multivalued physical response), behavior-first modeling may preserve more meaning than forcing a direction of computation. If the question requires algorithmic state update, a coalgebra/state representation may be preferable or may be derived from the behavior under realization hypotheses. Neither automatically subsumes the other at the level of computational interfaces.

**Related notes:** Note 03, Note 07, Note 15.

---

## 06 — Fibrations, institutions, and doctrines: three different law/parameter interfaces

**Origin:** chat L723–759, L800–823, L882–910, L477–514. **Status:** corrected typing; extensions identified.

## Fibrations: varying *families of systems* over a base

A fibration \(p:\mathcal E\to\mathcal B\) has a base of contexts/parameters/signatures and fibers \(\mathcal E_b\) of objects over \(b\). Along \(u:b\to b'\), a chosen cartesian lifting gives **contravariant reindexing**

\[
u^*:\mathcal E_{b'}\longrightarrow\mathcal E_b.
\]

It is incorrect to interpret this as arbitrary forward transport of one system to any new law setting. Reindexing generally *pulls back* a system already living over the target of \(u\). Forward transport is extra, often an opfibration or suitable adjoint, and does not always exist. Different choices of cleavages affect strictness of functoriality.

**A use case:** model families indexed by admissible parameter domains, sensor configurations, or signatures, where changing the indexing context must induce coherent restriction of models.

## Institutions: separate formal laws from models satisfying them

An institution has signature category \(\mathbf{Sig}\), a sentence functor \(\operatorname{Sen}:\mathbf{Sig}\to\mathbf{Set}\), a contravariant model assignment \(\operatorname{Mod}:\mathbf{Sig}^{op}\to\mathbf{Cat}\), and satisfaction relations. For \(\sigma:\Sigma\to\Sigma'\),

\[
M'\models_{\Sigma'}\operatorname{Sen}(\sigma)(\varphi)
\iff
\operatorname{Mod}(\sigma)(M')\models_{\Sigma}\varphi.
\]

This says that satisfaction is respected by translation of **signatures**, not that physical laws are true in nature or that every model admits a numerical solution. Source: [Goguen on institutions](https://cseweb.ucsd.edu/~goguen/projs/inst.html); [institution survey](https://iep.utm.edu/insti-th/).

**A use case:** exchanging law signatures or theories while making changes to vocabulary, equations, and satisfaction explicit.

## Doctrines: predicate operations indexed by contexts

A common categorical doctrine is a functor of predicates \(P:\mathcal C^{op}\to\mathbf{Poset}\), often with fibers carrying logical structure and reindexing by substitution. Quantifiers, equality, and connectives require extra adjoints/laws. This is **not** synonymous with an institution: one starts from indexed predicates and proof-relevant structure, the other from signatures, sentences, models, and satisfaction. They can be connected, but not by relabeling one as the other.

## Limits of the proposed combination

An institution can say that \(M\) satisfies equations; a fibration can reindex models with their parameters; an actegory can encode some genuine operator action on systems. The three do not automatically compose into a single theory. Before integrating them, specify whether the base indexes *syntax*, *physical parameters*, *geometric carriers*, or *assumptions about observations*. A parameter value such as mass \(m\) does not necessarily define a morphism to another value \(m'\), and changing it may change the topology of the solution set.

**Related notes:** Note 03, Note 04, Note 20.

---

## 07 — Wiring formalisms: interfaces, assembly, and hidden state

**Origin:** chat L665–693, L761–799, L1958–2013, L2088–2211. **Status:** architecture retained, typing corrected.

The salient problem is **not** just decomposing a large equation into smaller ones. It is defining a syntax of connections, an interpretation of components, and rules for eliminating/hiding internal interface variables without losing required guarantees.

## Distinguish four layers

**Typed boundaries:** which ports exist and what they carry; possibly including signal direction, protocols, clocks, units, energy ports, or resource capabilities.

**Component behavior:** what an attached subsystem does, or which histories it permits, for those boundary variables.

**Wiring operation:** how external and internal boundaries are connected, synchronized, duplicated, identified, or hidden. This requires typing and may require copying/deleting structure absent from general monoidal categories.

**Contract composition:** which assumptions, guarantees, and failures survive the wiring operation. This does not follow merely from the syntax being well-typed.

## Several legitimate syntaxes

- **Decorated cospans:** a span-like interface shape \(X\to N\leftarrow Y\) in which the apex carries a decoration (e.g., a graph or dynamical structure); composition generally uses pushouts plus compatible decoration operations.
- **Structured cospans:** maps \(L(X)\to N\leftarrow L(Y)\), where a functor \(L\) chooses how interface objects embed as internal structures. This is a different construction, not just another name for decorated cospans. [Baez–Courser](https://arxiv.org/abs/1911.04630).
- **Polynomial interfaces:** dependent input/output shape can capture choices of positions and directions; a composition semantics for the particular polynomials must still be supplied.
- **Double categories/equipment:** distinguish horizontal systems or proarrows from vertical interface maps/refinements; 2-cells encode compatibility. Neither direction has a canonical physical interpretation until defined.
- **Operads/colored operads:** express a syntax of hierarchical plugging; an algebra of the operad provides the semantic operations.

## Minimal typed assembly contract

Let \(w:(B_1,\ldots,B_n)\to B\) be an allowed wiring. An interpretation needs operations

\[
\mathsf{Asm}_w:\mathsf{Comp}(B_1)\times\cdots\times\mathsf{Comp}(B_n)\to\mathsf{Comp}(B),
\]

compatible with nested wiring and identities, strictly or up to coherent isomorphism. If \(\mathsf{Comp}(B)\) is a **category**, the action of wiring on component morphisms/refinements must be specified too. The conversation's \(\mathcal R_B\) alternately denoted processes as arrows and systems as objects; that ambiguity destroys the types of its assembly formulas.

For internal stateful components \(f:S_A\times I\rightharpoonup S_A\times M\) and \(g:S_B\times M\rightharpoonup S_B\times O\), serial composition carries the product state \(S_A\times S_B\). It is defined when \(f\) runs **and its particular output** lies in the domain of \(g\). Local domains alone are insufficient (see Note 08).

## What remains separate

Wiring may be possible without solving an instantaneous feedback equation. It may be semantically defined but unsafe under an energy budget. Local contracts may conflict when hidden states share an unmodeled resource. An assembly theorem needs explicit compatibility and observation assumptions.

**Related notes:** Note 05, Note 08, Note 11, Note 20.

---

## 08 — Restriction categories: the algebra of *definedness*

**Origin:** chat L998–1055, L1435–1703, L1958–2118, L2635–2737. **Status:** definition corrected and boundaries identified.

## The actual structure

For a partial function \(f:X\rightharpoonup Y\), the restriction \(\bar f:X\rightharpoonup X\) is the partial identity on the domain \(D_f\). In a restriction category, each arrow is supplied with such an idempotent, satisfying (with usual right-to-left composition):

\[
\begin{aligned}
f\bar f&=f,\\
\bar f\bar g&=\bar g\bar f\quad(\text{common source}),\\
\overline{g\bar f}&=\bar g\bar f\quad(\text{common source}),\\
\bar g f&=f\,\overline{gf}\quad(\text{composable }f,g).
\end{aligned}
\]

These axioms are *algebraic*. They do not introduce a new computation that decides where an arbitrary partial program terminates. The restriction operation is part of the chosen category's structure. For split restriction categories there is a representation by categories of partial maps, with appropriate domain-monic data. See [Cockett–Lack](https://www.sciencedirect.com/science/article/pii/S0304397500003820).

## The precise compositional gain

For partial functions,

\[
D_{gf}=D_f\cap f^{-1}(D_g).
\]

A downstream precondition must be pulled back through the **actual upstream behavior**. Two total functions with identical domains but different outputs can yield different composite domains. Let \(f_0(*)=0\), \(f_1(*)=1\), and let \(g\) be defined only at \(0\). Then \(gf_0\) is total and \(gf_1\) nowhere defined. Thus **domains alone are not a sufficient interface for composition**.

For independent Cartesian products, \(D_{f\times g}=D_f\times D_g\); shared resources or feedback require more semantics and may defeat this independence.

## Five tempting but false identifications

1. \(\bar f\) is not a total Boolean-valued `enabled?` method. In effectful or computable settings, producing a restriction result may itself diverge.
2. Definedness is not safety. An unsafe state transition can be total, and a safe admissible evolution may be only locally defined.
3. Undefinedness is not a returned diagnostic: \(f:X\rightharpoonup Y\) differs from \(f:X\to Y+E\), which reports typed errors; blocking, crash and partial side effects need further structure.
4. A physical law's *approximation regime* is not necessarily the domain of its mathematical function. Defining \(\bar f\) to capture regime validity is a **chosen restriction**, not an automatic property of an equation.
5. An internal \(\bar\delta:S\times I\to S\times I\) does not automatically induce a boundary \(\bar C:I\to I\). Hidden state must be dealt with first.

## A structural obstruction for nondeterminism

Let \(R(x)=\{0,1\}\) and let \(g\) be defined only on \(0\). If \(\bar R\) means identity on *existentially enabled* inputs, then \(\bar g\circ R\) retains only the \(0\)-branch, but \(R\circ\overline{g\circ R}\) retains both branches. The last restriction axiom fails. Arbitrary relations cannot receive this naive existential-domain restriction structure.

## Useful extent

Restriction categories are appropriate when the *chosen process composition* has the required partiality laws. They are not a universal feasibility checker, safety calculus, or modal logic. Related modal predicates can be built over a compatible predicate semantics; see Note 09.

**Related notes:** Note 07, Note 09, Note 19.

---

## 09 — From internal actions to observable capabilities

**Origin:** chat L1435–1441, L1564–1678, L2215–2364, L2635–2737. **Status:** corrected formal bridge and independent derivations.

A controller acts from **information**, not directly from an internal state it cannot observe. Thus actual enabledness, *possible* enabledness, *guaranteed* enabledness, and *known* enabledness should not be silently identified.

Let \(r:S\to O\) be a readout and \(D_a\subseteq S\) the domain of action \(a\). For nonempty current information set \(B_h\subseteq S\) obtained from the complete admissible history \(h\):

\[
\mathrm{May}_a(h)\iff\exists s\in B_h:s\in D_a,\qquad
\mathrm{Must}_a(h)\iff\forall s\in B_h:s\in D_a.
\]

In the usual information-set model, **knowing** that \(a\) is enabled corresponds to the universal condition, assuming the model itself is trusted. Probabilistic confidence, almost-sure truth, adversarial robustness, and statistical detection are distinct semantics.

## Exact observable action: a clean iff criterion

For \(r:S\twoheadrightarrow O\) and a partial deterministic update \(f:S\rightharpoonup S\), an exact partial observation-level map \(\hat f:O\rightharpoonup O\) satisfying \(\hat f\circ r=r\circ f\) exists **if and only if**:

1. **Domain saturation:** \(r(s)=r(t)\Rightarrow (s\in D_f\iff t\in D_f)\).
2. **Output consistency:** if \(r(s)=r(t)\) and both updates are defined, \(r(f(s))=r(f(t))\).

Necessity follows by equality of the domains and outputs of the two partial composites. Sufficiency follows by choosing any representative of each observation fiber, since both definedness and output are independent of the representative. If either condition fails, an exact deterministic observation-level command is not available. Options include belief-state transitions, observation histories, relations, or sound overapproximations—**different interface contracts**.

## An indispensable quantifier distinction for control

\[
\forall s\in B_h\,\exists a:\mathrm{Safe}(s,a)
\quad\not\Rightarrow\quad
\exists a\,\forall s\in B_h:\mathrm{Safe}(s,a).
\]

Two indistinguishable states can each have a different safe action but no single safe action in common. A usable controller must choose its action from observations/history. In multi-step settings, replace an isolated \(a\) by a strategy/policy on available histories and specify the objective (finite reachability, invariance, liveness, discounted performance, etc.).

## The actual modal bridge

For a deterministic partial \(f:X\rightharpoonup Y\) and \(Q\subseteq Y\):

\[
\langle f\rangle Q=\{x\in D_f:f(x)\in Q\},\qquad
[f]Q=(X\setminus D_f)\cup\langle f\rangle Q.
\]

Thus \(\langle f\rangle\top=D_f\), but \([f]Q\) is vacuously true where \(f\) is undefined. Diamond and box coincide **on the domain**, not globally. The slogan \(\bar f=\langle f\rangle\top\) is well-typed only after domain predicates are identified with their corresponding partial identities. Ordinary restriction structure lacks epistemic, temporal, and strategic modalities until extra semantics is specified.

A proof-carrying action can be typed \(\{x:X\mid D_f(x)\}\to Y\) in a compatible refinement-type theory, but a runtime-deciding guard or an arbitrary dependent-type interpretation does not follow just from the existence of \(\bar f\).

**Related notes:** Note 02, Note 08, Note 19, Note 21.

---

## 10 — Relation-first dynamics, allegories, Kleisli categories, and effects

**Origin:** chat L920–946, L1239–1351, and L1682–1742. **Status:** distinctions corrected; formal comparison expanded.

The valuable move here is refusing to assume that every physical or computational transition is a single-valued function. There are **several** ways to relax that assumption, and they preserve different information.

## Bare relations

A transition \(R\subseteq X\times Y\) relates one input to zero, one, or several outputs. Composition is existential elimination:

\[
(x,z)\in S\circ R\iff \exists y:\ (x,y)\in R\land(y,z)\in S.
\]

Relational converse \(R^\circ\subseteq Y\times X\) reverses pairs. **Converse is not inverse:** a many-to-one law remains multivalued backward. Bare relations provide no probability, duration, optimality, or distinction between deadlock and a failed precondition.

## Allegories

An allegory is a locally ordered relation-like category with hom-set binary meets, an identity-on-objects contravariant involution \((-)^\circ\), and the **modular law**. For composable \(R:X\to Y\), \(S:Y\to Z\), and \(T:X\to Z\), its relational form is

\[
(S\circ R)\wedge T\ \le\ S\circ(R\wedge S^\circ\circ T).
\]

This is real extra algebra, not just “a category with converse and intersection.” \(\mathbf{Rel}\), with inclusion as order and intersection as meet, is the motivating example. When physical laws are implicit constraints, allegories support useful equational/inequational reasoning. They do not by themselves make constraint-solving executable. [Definition and modular law](https://ncatlab.org/nlab/show/allegory).

## Kleisli categories and typed effects

For a monad \(T\) on a suitable base category, Kleisli arrows \(X\to Y\) are base arrows \(X\to T(Y)\). Specific monads give different effects: powerset for nondeterminism; finite distributions for discrete probability; a subprobability construction for termination/mass loss; exceptions for typed errors; writer monads for accumulated monoid-valued logs or costs. Continuous-state stochastic kernels need measurable structure, not the naive finite-distribution monad.

The phrase **“Kleisli bicategories of relations/probability”** in the transcript does not specify one construction. To be meaningful, it needs a base bicategory or equipment, the appropriate higher monad/extension, 2-cells, and compatible composition laws. It should remain a *reserve research candidate* rather than a fully defined theory.

## Effect combinations are not free

If a computation has both nondeterminism and probability, its semantic type and resolution order matter: probability over sets of outputs, sets of distributions, probabilistic choice before/after adversarial choice, and mixtures of these are inequivalent. Composing effects can require a distributive law or a bespoke monad; such a law may fail to exist.

Likewise, an arbitrary nondeterministic relation equipped with “restriction = identity on existential domain” violates a restriction axiom; see Note 08. Do not impose restriction semantics on a Kleisli or relational category without checking the axioms.

## Quantaloids and weighted relations

A quantaloid has ordered homs admitting arbitrary joins, with composition preserving joins in each argument. Relations form an example. Weighted matrices and enriched categories can represent costs, similarities, or reachability under an appropriate quantale. **One must choose the order and semiring/quantale convention:** minimum-cost algebra is not automatically probability algebra, nor is a “value of a path” necessarily a physical law.

**Use when:** the observed phenomenon is an admissibility relation, constraint network, nondeterministic protocol, weighted route problem, or genuinely stochastic transition. The choice turns on which multiplicities, measures, and compositions must survive.

**Related notes:** Note 05, Note 08, Note 19.

---

## 11 — Feedback is an operation with its own existence and coherence obligations

**Origin:** chat L918–927, L1988–2009, L2493–2539. **Status:** corrected; counterexamples derived.

Not every notion of wiring includes feedback. Even when there is a diagrammatic loop, its semantics could mean an instantaneous algebraic constraint, a delayed update, an infinite interaction trace, a fixed point, or a stateful protocol. Those interpretations are not interchangeable.

## Instantaneous feedback as a relation

Take \(F:X\times U\rightharpoonup Y\times U\). One possible semantics is

\[
(x,y)\in\operatorname{Fb}(F)
\iff\exists u\in U:\ F(x,u)=(y,u).
\]

This is a **relation**, not necessarily a partial function. With \(X\) a singleton and \(Y=U=\{0,1\}\):

- \(F(*,u)=(u,1-u)\) has no feedback solution.
- \(F(*,u)=(u,u)\) has two external outcomes.

Existence of a fixed point does not establish a deterministic closed-loop update. Uniqueness of the internal fixed point suffices, but is not necessary, for an unambiguous external result: several internal solutions may share the same visible output.

## A delayed loop is not an algebraic fixed point

A recurrence \(u_{t+1}=h(u_t)\) with a specified initial state is well-defined even if \(h\) has no fixed point or its trajectories oscillate. Treating oscillation as undefinedness confuses liveness/stability/specification failure with mathematical nonexistence. For continuous-time feedback, causal well-posedness can require existence, uniqueness, regularity, and non-Zeno conditions, depending on the model.

## Traced categories and partial traces

A traced symmetric monoidal category supplies a trace \(\operatorname{Tr}^U_{X,Y}:\mathcal C(X\otimes U,Y\otimes U)\to\mathcal C(X,Y)\) obeying trace axioms. **Its presence is additional structure**, not guaranteed by a restriction category or cospan syntax. “Trace defined only for some arrows” is different from “a total trace produces an arrow representing a partial function.” For a formal partially traced structure, see [Malherbe–Scott–Selinger](https://arxiv.org/abs/1107.3608).

The \(\mathrm{Int}\) construction and geometry-of-interaction approaches are useful where feedback/interaction itself is primitive. Their categorical feedback is not automatically physical time evolution, numerical iteration, or control-theoretic stability.

## A concrete abstraction obstruction

A coarse external relation \(R\subseteq I\times O\) may be adequate for one-shot composition but inadequate for feedback contexts. In nondeterministic dataflow, processes with the same ordinary I/O relation can have different feedback behavior. The relevant abstraction must preserve the timing/causal dependency of interactions, not just a set of possible input/output pairs. See Saunders-Evans and Winskel, *Event Structure Spans for Nondeterministic Dataflow* (author-hosted research cited in the earlier audit).

**Selection condition:** choose the loop semantics first. Only then ask whether a trace, relation, fixed-point operator, guarded recursion, or temporal transition system implements it faithfully.

**Related notes:** Note 02, Note 07, Note 13, Note 20.

---

## 12 — Local-to-global behavior: presheaves, sheaves, and stacks

**Origin:** chat L682–683, L846–865, L934–935, L1439–1441. **Status:** common categorical errors corrected; application examples expanded.

A sheaf should be chosen because the system genuinely has **local data on overlapping domains whose compatibility and gluing matter**. It is not a mandatory upgrade from partial observability, nonstationarity, or distributed execution.

## The typed construction

For a topological space \(X\), a presheaf of sets is \(F:\mathsf{Open}(X)^{op}\to\mathbf{Set}\). For \(V\subseteq U\), the arrow \(F(U)\to F(V)\) is a **restriction map**, not a time-evolution map from an earlier time to a later time. A sheaf requires compatible sections on a cover of \(U\) to glue **uniquely** to a section of \(F(U)\).

A typical application is a sheaf of solutions of a local differential equation on a fixed geometric domain: solutions restrict to smaller open sets, and agreeing smooth solutions glue. Boundary conditions or global consistency constraints can be represented, but may introduce additional structure or restrict admissible global sections.

## Three logically different obstructions

1. A chosen family of local sections **disagrees on overlaps** and therefore cannot glue.
2. Local solutions on some domains exist but **no global solution of the selected constrained problem** exists.
3. A particular partial solution **cannot extend** into a specified larger domain.

None implies an empty stalk. A stalk summarizes germs near a point; global obstruction can arise while all local stalks are nonempty. Conversely, an empty section over one domain may arise from constraints unrelated to a local singularity.

**Toy witness:** constant-valued local solutions \(s_1\equiv0\) on \((-1,0.2)\) and \(s_2\equiv1\) on \((-0.2,1)\) disagree on their overlap. This family cannot glue, even though globally constant solutions exist. Thus “incompatible local choices” and “no global model” are distinct.

## When a stack is genuinely required

A set-valued sheaf forgets automorphisms of local objects. A stack can retain groupoid-valued data and coherent descent up to isomorphism. This is significant for gauge-related field configurations, bundles, or moduli problems, where locally equivalent presentations may need transition isomorphisms satisfying cocycle conditions. **Merely having many agents or heterogeneous data does not force a stack.**

## What gluing does *not* do

It neither finds local sections, proves computability, synthesizes a feasible trajectory, minimizes cost, nor licenses arbitrary forward extrapolation. Replanning via “choose a new local section and glue” is valid only if the new sections exist, agree on overlaps, satisfy boundary/history constraints, and support the desired objective. The relevant solution sheaf must have been constructed.

**Related notes:** Note 15, Note 17, Note 20.

---

## 13 — Events and causal structure instead of one global state clock

**Origin:** chat L918–946, L1179–1234, L1355–1387. **Status:** retained with definitions and boundary conditions corrected.

## Prime event structures

A common presentation is \((E,\le,\#)\), with a causal partial order \(\le\) and symmetric irreflexive conflict \(\#\), subject to conflict heredity (e.g., \(a\#b\le c\Rightarrow a\#c\)) and often finite-cause requirements. A **configuration** is a conflict-free, downward-closed set of events representing an admissible finite or infinite history. This model retains concurrent alternatives that a single arbitrary linear ordering can obscure. [Winskel's work](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-95.html).

**Example:** event \(a\) authorizes both independent changes \(b\) and \(c\). The configuration \(\{a,b,c\}\) need not privilege the chronology \(a,b,c\) over \(a,c,b\). By contrast, mutually conflicting events \(d\#e\) cannot be in the same configuration.

This is not “dynamics without states”: configurations **are state-like objects**, ordered by inclusion. The value of the presentation is the **provenance of concurrency, conflict, and causality**, not absence of a state space.

## What the event order does and does not encode

Causal precedence is not elapsed time, metric duration, real-time deadline, or a unique global time coordinate. Two unordered events may be concurrent under the chosen semantics, but their concrete implementations can still share a resource and therefore interfere. Event independence must be justified in the modeled operational regime.

Event-structure spans can carry more precise interaction semantics than coarse I/O relations in feedback settings. This is a candidate for preserving concurrency-sensitive substitutability, not a universal replacement for timed transition systems.

## Causal categories and causal sites are not synonyms

Different categorical causality theories have distinct objects and axioms. Christensen–Crane **causal sites**, for example, relate regions through both containment and causal precedence with compatibility requirements; the structure is richer than one causal poset. A relativistic causal ordering can constrain which influences propagate, but **does not by itself generate the dynamics or a deterministic evolution law**.

## When this cut is worth preserving

Use events/causal structures where a linear transition trace forgets essential independence, synchronization, or branching information. Distinguish actual physical causality, causal precedence defined by a model, and causal inference from observational data: their validity stories differ.

**Related notes:** Note 11, Note 19, Note 22.

---

## 14 — Diffeological and Frölicher spaces: smoothness without manifold charts

**Origin:** chat L976–994, L1059–1110. **Status:** source idea retained; mathematical claims calibrated.

## Two different generalized smooth structures

A **diffeological space** is a set \(X\) supplied with designated *plots* \(p:U\to X\), where \(U\) ranges over open subsets of Euclidean spaces. Constants are plots; smooth reparameterizations of plots remain plots; and locally compatible plots glue as plots. A map \(f:X\to Y\) is smooth if it takes plots of \(X\) to plots of \(Y\) by composition. This gives useful subset, quotient, product, and function-space constructions even when the resulting objects are not ordinary finite-dimensional manifolds. [Iglesias-Zemmour](https://doi.org/10.1090/surv/185).

A **Frölicher space** is presented using mutually determining classes of smooth curves \(c:\mathbb R\to X\) and smooth real-valued functions \(\varphi:X\to\mathbb R\), constrained by smoothness of \(\varphi\circ c\). The two theories are related but **not definitionally identical**. Plot-side smoothness and function/curve-side smoothness preserve different primitive information.

## Decomposition payoff

The carrier \(X\) and its smooth structure can be changed without first assuming a compatible atlas of ordinary manifold charts. This is useful for spaces of maps/fields, quotient state spaces, singular orbit spaces, or nonstandard smooth parameter spaces. The gain is a better **substrate for expressing laws**, not a law generator.

It is tempting to say that choosing a diffeology automatically gives well-defined tangent bundles, vector-field flows, or a smooth hybrid controller. It does not. Several inequivalent tangent constructions are possible for generalized spaces, and existence/uniqueness of dynamical solutions still requires hypotheses. A space with mixed discrete and continuous modes also needs a **hybrid execution semantics**; smooth plots alone do not define resets or jump admissibility.

## Example discrimination

If quotienting a manifold by symmetries produces a singular space on which the *quotient of smooth observations* remains meaningful, diffeological methods may be more faithful than forcing the quotient into a manifold structure. If the task is only finite-state reachability, this extra smooth machinery contributes no necessary control operation.

**Terminology reserve:** the source says “Ehresmann/Frölicher/diffeological spaces.” “Ehresmann space” was not specified and cannot be repaired without a definition; it could point toward several different Ehresmann-associated constructions. It is not part of this note's asserted equivalence.

**Related notes:** Note 15, Note 17.

---

## 15 — Weil functors, jets, Cartan distributions, and the variational bicomplex

**Origin:** chat L929–935, L1114–1175, L948–971. **Status:** underexplained candidates developed as an organized mathematical note; some content is external expansion.

The shared theme is **separating finite-order differential information, differential equations, and actual solutions**. These constructions are related, but are not one interchangeable “infinitesimal dynamics” framework.

## Weil algebras and functors

A Weil algebra \(A\) over \(\mathbb R\) is a finite-dimensional commutative local \(\mathbb R\)-algebra with residue field \(\mathbb R\) and a nilpotent maximal ideal. The canonical example is the dual numbers

\[
A=\mathbb R[\varepsilon]/(\varepsilon^2).
\]

On a suitable manifold category the corresponding Weil functor \(T^A\) produces \(T^A M\), a space of \(A\)-infinitesimal points; for dual numbers, \(T^A M\cong TM\). Crucially,

\[
T^A\circ T^B\cong T^{A\otimes B}
\]

under the standard hypotheses. This gives a genuine functorial **operator algebra of infinitesimal probes**, and is an interesting connection to actegories not developed in the chat. It does *not* create a vector field, law of motion, or flow on \(M\). The heuristic \(M^A\) is internal-point notation in suitable geometry, **not** ordinary set-theoretic exponentiation of a manifold by an algebra. [Kriegl–Michor](https://www.mat.univie.ac.at/~michor/kmsbookh.pdf).

## Jet bundles: finite derivative data of sections

For a configuration bundle \(\pi:E\to M\), \(J^kE\) records \(k\)-jets of local sections: their derivatives through order \(k\), identified at each base point. A differential equation can be represented as a submanifold or, more generally, a subset/subspace \(\mathcal E\subseteq J^kE\) with specified regularity. A section \(s\) is a solution when its prolongation \(j^ks\) lies in \(\mathcal E\).

This separates **equation locus** from **holonomic solution**. A point satisfying the equation in jet space is not automatically the jet of a global solution satisfying boundary data. Prolongation and integrability/compatibility conditions matter.

## Cartan distribution and diffieties

Jet bundles carry **contact geometry** distinguishing legitimate jets of sections from arbitrary motions in jet coordinates. On infinite jets, the Cartan distribution is spanned locally by total-derivative operators; it encodes the infinitesimal directions tangent to prolonged solution graphs. A **diffiety** is a geometric formalism for a suitably regular/involutive infinite prolongation of a PDE system. No ordinary finite-dimensional vector field is guaranteed.

## Variational bicomplex

On \(J^\infty E\), differential forms admit a horizontal/vertical bigrading, with

\[
d=d_H+d_V,
\qquad d_H^2=d_V^2=d_Hd_V+d_Vd_H=0.
\]

This organizes total derivatives, variation, Euler–Lagrange operators, boundary terms, and (under suitable hypotheses) conservation laws. It is especially useful when asking whether a differential equation is variational, how a current depends on a Lagrangian, or which terms are exact/boundary contributions. It does **not** make every PDE an Euler–Lagrange equation. [Ian Anderson, *The Variational Bicomplex*](https://ncatlab.org/nlab/files/AndersonVariationalBicomplex.pdf).

## Selection rule

Use Weil functors for *functorial infinitesimal probes*; jets for *differential laws as constraints on derivatives*; Cartan geometry for *holonomicity and prolongation*; and the variational bicomplex for *variation, boundary terms, and conservation identities*. These constructions may interoperate but do not determine dynamics without an equation, boundary conditions, and a solution notion.

**Related notes:** Note 03, Note 12, Note 16.

---

## 16 — Dirac structures and Tulczyjew triples: constraints, energy, and dynamics

**Origin:** chat L936–938, L948–958, L465–488. **Status:** external technical expansion of source-listed techniques; not a universal open-system prescription.

These are strong examples of **representation by constrained relations** rather than arbitrary explicit state updates. Their value is particularly high when physical interfaces carry energy.

## Linear Dirac structure: a power-conserving relation

Let \(V\) be a finite-dimensional real vector space. Equip \(V\oplus V^*\) with the symmetric bilinear form

\[
\langle(v,\alpha),(w,\beta)\rangle=\alpha(w)+\beta(v).
\]

A **linear Dirac structure** \(D\subseteq V\oplus V^*\) is maximally isotropic under this pairing (equivalently \(D=D^\perp\)). Therefore, for every \((f,e)\in D\), \(e(f)=0\): this gives an abstract power-conservation identity for conjugate flow/effort variables. For smooth manifolds, one ordinarily also requires suitable involutivity under the Courant bracket for an **integrable** Dirac structure. A merely maximally isotropic subbundle is sometimes called an *almost Dirac* structure.

The Dirac structure alone is **not** a complete dynamical system. It provides an interconnection/constraint geometry. An energy function \(H\), storage flow, dissipation law, inputs, and boundary conditions select evolution. A typical port-Hamiltonian relation is

\[
(-\dot x,\mathrm d H(x),f_{\mathrm p},e_{\mathrm p})\in D,
\]

with sign conventions chosen for the storage port. Appropriate power balance follows from isotropy; dissipation and passivity require additional elements/inequalities. Power conservation is not reversibility, existence, uniqueness, or asymptotic stability.

For particular well-posed interconnection classes, composing Dirac structures preserves an energy-compatible port-Hamiltonian model; those are substantive compositional results rather than a generic consequence of any wiring. [Van der Schaft, overview](https://doi.org/10.4171/022-3/65); [interconnection theorem](https://www.sciencedirect.com/science/article/pii/S0005109806003682).

## Tulczyjew triple: relate Lagrangian and Hamiltonian presentations

For a configuration manifold \(Q\), the triple exploits canonical maps between

\[
T^*(TQ),\qquad T(T^*Q),\qquad T^*(T^*Q).
\]

One canonical map \(\alpha_Q:TT^*Q\to T^*TQ\) and the symplectic identification \(\beta_Q:TT^*Q\to T^*T^*Q\) allow dynamics to be encoded as submanifolds/relations. For smooth \(L:TQ\to\mathbb R\) and \(H:T^*Q\to\mathbb R\), representative dynamics are

\[
D_L=\alpha_Q^{-1}(\mathrm d L(TQ)),
\qquad
D_H=\beta_Q^{-1}(\mathrm d H(T^*Q)),
\]

with a fixed sign convention for \(\beta_Q\). When a Legendre transform is regular, these presentations can correspond. For singular Lagrangians there may be primary constraints, gauge freedom, or no unique Hamiltonian vector field, so “same physics in both forms” is not automatic. [Grabowska–Grabowski](https://www.aimsciences.org/article/doi/10.3934/jgm.2013.5.445).

## How the decompositions differ

**Dirac:** split energy storage, port power-conservation/interconnection, and admissible flows. **Tulczyjew:** relate variational and cotangent-bundle dynamical presentations without committing prematurely to an explicit evolution vector field. **Courant algebroid:** an ambient bracket/pairing/anchor structure in which geometric Dirac structures can be defined and studied.

These do not solve the general “vary every physical law freely” problem: the geometric substrate, energy variables, and compatibility of interconnections impose real constraints.

**Related notes:** Note 03, Note 10, Note 15.

---

## 17 — Groupoids, stacks, and derived solution spaces: do not erase witnesses too early

**Origin:** chat L934–935, L948–971 and related stack mentions. **Status:** an elaboration of a short source-list entry; research candidate, not a concluded architecture.

The decomposition question here is *what a space of solutions forgets when it is reduced to a set of equivalence classes*. In gauge theories and singular constraint problems, two forms of information may matter even after the ordinary solution set has been computed:

1. **Automorphisms/equivalence witnesses:** how solutions are related and what stabilizers remain.
2. **Nontransversality and infinitesimal obstruction data:** why a solution may be singular or fail to deform smoothly with a parameter.

## Groupoids and stacks: equivalence is structured data

If a group \(G\) acts on a space \(X\), the orbit set \(X/G\) identifies equivalent elements but discards stabilizer data. The **action groupoid** retains objects \(x\in X\) and arrows \(x\xrightarrow{g}gx\). A quotient stack \([X/G]\) (in a suitable geometric category/site) retains this groupoid-like moduli information and descent under changes of local presentation.

For instance, two orbits may each become one point in an ordinary quotient even though the corresponding stabilizer groups differ. Such a collapse is unacceptable if the consumer asks about residual gauge symmetries or local deformation types. It may be harmless if the only question is the value of a gauge-invariant scalar observable.

## Derived intersections: preserve hidden constraint geometry

Classical simultaneous constraints often form an intersection \(Z(f)\) or critical locus \(\{\mathrm dS=0\}\). If constraints meet nontransversely, the ordinary set or scheme can suppress higher intersection/deformation information. **Derived** intersections and derived critical loci retain additional homotopical/algebraic structure; tangent–obstruction complexes can indicate singular infinitesimal behavior. A sharper example uses **redundant constraints** \(f:\mathbb A^1\to\mathbb A^2\), \(f(x)=(x,x)\). The classical scheme-theoretic zero locus is the reduced point \(x=0\) because the ideal \((x,x)=(x)\). The *derived* zero locus retains a degree-\(-1\) Koszul homology class: for the Koszul complex of \((x,x)\), the cycle \((1,-1)\) is not a boundary over \(\mathbb R[x]\), while its multiple by \(x\) is. Hence \(H^{-1}\cong\mathbb R[x]/(x)\). The redundant-equation obstruction is invisible to the ordinary scheme, not merely to its underlying set.

This does not automatically yield a physical stability estimate, a numerical solver, or global existence. A derived tangent or obstruction complex is **algebraic infinitesimal information**. Analytic dynamics require separate regularity, topology, or PDE analysis.

## Relation to law variation

A parameterized family of laws may change not just the number of solutions but their stabilizers, multiplicities, and singularity types. A model indexed only by solution sets cannot detect all such changes. Stacks/derived geometry become appropriate when the downstream question *actually consumes* those distinctions.

**Diagnostic:** before adopting higher geometry, state the missing datum that the ordinary quotient loses and give a consumer that requires it. Without such a consumer, the additional machinery is overhead rather than demonstrated adequacy.

**Related notes:** Note 02, Note 12, Note 15.

---

## 18 — Lenses, open games, and interaction semantics

**Origin:** chat L679–680, L825–844, L922–926. **Status:** corrected scope and added discriminating definitions.

The common intuition is **bidirectional or interactive composition**, but these constructions answer different problems.

## Lenses/optics: a typed forward/backward interface

One elementary lens shape is a pair

\[
\mathrm{get}:X\to Y,\qquad \mathrm{put}:X\times R\to S,
\]

viewed as a morphism \((X,S)\to(Y,R)\). For an ordinary lawful state-update lens, additional lens laws such as Get–Put and Put–Get may be required; the general optic/lens shape alone does **not** ensure they hold. A backward map is not by itself a causal controller, optimizer, derivative, or gradient. It transports a *specified backward type of information*.

## Open games: play, coplay, and equilibrium are distinct data

A standard set-based open game includes a strategy set \(\Sigma\), a forward play map \(P:\Sigma\times X\to Y\), a backward coplay map \(C:\Sigma\times X\times R\to S\), and a context-indexed best-response/equilibrium selector. In the compositional game literature, **open games are morphisms** in a suitable monoidal category; they are not generally “strategy profiles as morphisms.” The additional best-response data is essential; play/coplay alone do not define a game. See [Ghani–Hedges–Winschel–Zahn](https://strathprints.strath.ac.uk/64265/) and [Hedges, Morphisms of Open Games](https://www.sciencedirect.com/science/article/pii/S1571066118300884).

Nash equilibrium existence is a separate theorem or failure of a selected strategy class. In every finite normal-form game with nonempty finite actions there is a mixed equilibrium; pure equilibrium may be absent. Accordingly, “morphism with no Nash equilibrium” is not a generic categorical exception handler.

## Dialectica and witness/counter-witness decomposition

Dialectica-style constructions distinguish choices/witnesses from challenges or counter-witnesses. This can clarify adversarial specification and test design **when the game/logic translation is defined**. The mere presence of two players or a minimax objective does not establish a Dialectica category of dynamical systems, nor does it yield a synthesis algorithm automatically.

## Geometry of interaction (GoI)

GoI and related traced/interaction semantics can model feedback-style token or information flow. Their operational content depends on how the interaction machine, trace, and observation are interpreted. A diagrammatic loop is not automatically a physical feedback law or a convergent iterative controller.

## Selection rule

Use lenses when there are well-typed forward and backward information channels; open games when strategic evaluation and best responses under composition matter; Dialectica when construction and challenge are genuinely dual in the selected logic; GoI when the behavior of interaction through feedback is itself the modeled primitive.

**Related notes:** Note 11, Note 20.

---

## 19 — Exceptions and replanning: distinguish the event, the judgment, and the obstruction

**Origin:** the user's toy environment chart L1435–1441 and the later feasibility/modal discussion L2635–2737. **Status:** corrected generalization; also incorporates the separately corrected environment table from the earlier exchange.

An “exception” is not one generic mathematical object. A reliable system model distinguishes at least these cases:

| Phenomenon | Object/judgment | Why it matters |
|---|---|---|
| Realized safety violation | \(s\notin K\) or trajectory violates \(\Phi\) | A completed bad behavior differs from failed execution |
| Failed precondition | \(x\notin D_f\) for a chosen partial command | Definedness is command-indexed |
| Explicit error result | \(f(x)=\mathrm{Err}(e)\) | Error label can support diagnosis/recovery |
| Unexpected observation | observation outside prediction or rejected by statistical test | Epistemic anomaly does not itself imply danger |
| Model-regime violation | assumptions for validity of approximate law no longer hold | A mathematical update may still exist |
| Infeasible continuation | no allowed policy/trajectory completes remaining task | Can occur *before* a deadline or safety failure |
| Policy failure under uncertainty | no common permissible action or winning strategy across information states | Must preserve observer/agent quantifiers |
| Feedback ill-posedness | no, many, or unstable solutions under a selected loop semantics | Existence, uniqueness, stability are separate |

## A precise finite-state safety example

Let \(S\) be finite, \(K\subseteq S\) safe, and \(A(s)\) enabled actions. For each \((s,a)\), let \(\mathrm{Post}(s,a)\subseteq S\) be a **nonempty** possible-successor set. Define

\[
\mathrm{CPre}(X)=\{s:\exists a\in A(s)\ [\mathrm{Post}(s,a)\subseteq X]\}.
\]

The maximal region from which a state-aware controller can keep the system in \(K\) forever is the greatest fixed point

\[
W=\nu X.\bigl(K\cap\mathrm{CPre}(X)\bigr).
\]

Here the **powerset lattice** supplies a computation on *predicates*, while the transition relation supplies the dynamics. No “lattice of states ordered by exceptionality” is needed. Under partial observability this state-aware fixed point need not implement an observation-based controller; the information-state game has to be constructed.

## Composition is not plan synthesis

Path concatenation, kernel composition, relational composition, tensor product, and sheaf gluing tell how **compatible pieces** combine. They do not select a feasible continuation or minimize an objective. A replanning interface must specify:

- what the current information/history is;
- what actions/policies are permissible;
- which effects of past execution are irreversible;
- which constraints apply to the full run or remaining horizon;
- which criterion selects among admissible continuations.

For a global ten-second deadline, two individually feasible six-second subplans are not jointly feasible; remaining time is part of the compositional interface. If a failed second step follows a first step with real side effects, a partial composite that only records “undefined” omits what replanning needs.

**Counterfactual test:** can a plan be declared locally valid in every component yet globally violate a resource, timing, synchronization, or information constraint? If so, the purported assembly theorem is missing premises.

**Related notes:** Note 07, Note 08, Note 09, Note 20.

---

## 20 — A typed architecture for heterogeneous open components

**Origin:** chat L1958–2013, L2183–2211, L2368–2631. **Status:** **design proposal**. It is not a construction established by the uploaded conversation.

## Build the smallest explicit interface before choosing an ambient category

Fix an allowed wiring syntax \(\mathsf W\) with boundary types \(B\) and composition of diagrams. For each boundary, choose:

\[
\mathsf{Impl}(B)\quad\text{(internal implementations)},
\qquad
\mathsf{Beh}(B)\quad\text{(external behaviors)}.
\]

Supply an interpretation \(\beta_B:\mathsf{Impl}(B)\to\mathsf{Beh}(B)\). If these are **categories**, specify what their arrows are—simulations, parameter changes, refinements, or executable transitions. The conversation uses all these interpretations but never chooses among them. This matters for the type of every categorical formula.

For an allowed wiring \(w:(B_1,\ldots,B_n)\to B\), specify both implementation assembly and behavior assembly. The central proposed law is

\[
\beta_B(\mathsf{Asm}^{\mathsf{Impl}}_w(C_1,\ldots,C_n))
\cong
\mathsf{Asm}^{\mathsf{Beh}}_w(\beta_{B_1}C_1,\ldots,\beta_{B_n}C_n),
\]

with compatibility under nested wiring. Use equality for a strict set-level interpretation, a coherent isomorphism for a suitable categorical one, or a *directed simulation/inclusion* for a sound abstraction. An unqualified \(\cong\) is not an excuse to ignore which observations are retained.

## Four independent proof obligations

**Typing:** every composition has matching ports, state threading, protocol conventions, and clock/resource interfaces. Stateful \(S\times I\rightharpoonup S\times O\) components do not automatically become arrows \(I\to O\) with state forgotten.

**Behavioral preservation:** \(\beta\) is compatible with the chosen wiring. Equivalence of one-step I/O relations may not suffice when feedback is allowed, so the external semantics may need histories, events, or more structured strategies.

**Contract preservation:** for local contracts \(K_i\), state and discharge explicit assumptions. A theorem should look like

\[
\bigwedge_i(C_i\models K_i)
\ \land\ \operatorname{Compatible}_w(K_1,\ldots,K_n)
\implies
\mathsf{Asm}_w(C_1,\ldots,C_n)\models K.
\]

The compatibility predicate must entail resource accounting, information requirements, synchronization, and—where applicable—well-posed feedback. Local validity does **not** imply global validity without it.

**Operational implementation:** decide which mathematical judgments can be computed or monitored, what uncertainties remain, and what control action is issued. A restriction idempotent or a logical theorem need not provide a decision procedure or online controller.

## Placement of the previously discussed tools

- **Coalgebra/behavioral theory:** candidate internal and/or boundary behavior models.
- **Actegory:** transformation of systems by a specified coherent operator algebra, if such an action exists.
- **Fibration/institution:** law/context indexing and satisfaction under change of signature.
- **Restriction category:** partial-process composition where its axioms hold.
- **Predicates/modalities:** contracts, enabledness propositions, temporal, epistemic, strategic judgments.
- **Wiring formalism:** operad/cospan/double-category/polynomial syntax and semantics.
- **Sheaves, event structures, Dirac structures:** extra behavioral geometry when required by locality, concurrency, or power-flow invariants.

These are *possible components*, not a theorem that the product of these abstractions exists or is faithful.

## Explicit stopping condition

A construction is successful only after one realistic component change can be made, its boundary effect computed, assembly rechecked, and at least one nontrivial guarantee proved or falsified. Until then this is a research agenda, not a general-purpose compositional calculus.

**Related notes:** Note 02, Note 07, Note 21, Note 22.

---

## 21 — Worked finite example: what survives the boundary?

**Status:** derived example, developed to test the chat's proposed interface. **Purpose:** expose the information lost by a hidden-state quotient and by exporting only local restriction predicates.

## Two serial components

Component \(A\) has hidden state \(s\in\{0,1\}\), no input, and a total update that emits \(m=s\) and toggles its internal state:

\[
\delta_A(s)=(1-s,m=s).
\]

Component \(B\) accepts \(m\in\{0,1\}\) only when \(m=0\), and returns `ok`:

\[
\delta_B(0)=\mathrm{ok},\qquad \delta_B(1)\ \text{undefined}.
\]

The serial composite is defined **exactly when \(s=0\)**. Even though \(A\) is total, its output can violate \(B\)'s precondition. Changing \(A\) to \(A'(s)=(1-s,m=0)\) preserves its full definedness domain but makes the composite always defined. Therefore \(\bar\delta_A\) alone does not determine \(\overline{\delta_B\circ\delta_A}\).

## Add an observation boundary

Suppose the external controller sees \(r(0)=r(1)=*\) and does **not** observe \(m\) before issuing a request that runs the series atomically. Its information set is \(B_* =\{0,1\}\). The composite command is **possibly enabled** but **not guaranteed enabled**:

\[
\exists s\in B_*:\ s=0,
\qquad
\neg\forall s\in B_*:\ s=0.
\]

No exact deterministic partial command \(\widehat\delta:*\rightharpoonup\mathrm{ok}\) can represent both internal cases with equality of definedness. If the controller instead can inspect \(m\) **before** invoking \(B\), it has a different protocol and can choose not to invoke \(B\) when \(m=1\). That is an interface change, not a solution to the original atomic-command problem.

## Explicit error semantics changes what is observable

Replace \(B\) by a **total** function returning either `ok` or `Err(input=1)`. The composite is now mathematically total, but still can produce a failure result. A recovery controller can use the diagnostic value; a mere partial function without such a result cannot. If \(A\) already toggled before this error, rollback also requires additional state/protocol data.

## What this one toy establishes

1. **Local valid-domain predicates are not enough for serial assembly.** Outputs matter.
2. **Internal definedness does not automatically descend to readout-level definedness.** Observation fibers matter.
3. **Atomic versus stepwise protocols differ.** Additional observation/control boundaries can improve achievable guarantees.
4. **Partial failure and reported error differ.** Recovery requires knowing intermediate effects.
5. **An architecture must choose the consumers.** A client asking only “might `ok` ever appear?” needs less information than a controller requiring guaranteed completion.

This example is deliberately finite and deterministic: none of these obstructions depends on sophisticated categorical machinery. Any purported general open-system calculus should represent them correctly before claiming support for stochastic feedback, PDEs, or changing physical laws.

**Related notes:** Note 02, Note 08, Note 09, Note 20.

---

## 22 — Discriminating probes and unresolved research questions

**Origin:** all of the conversation, especially L518–588, L915–971, L1958–1960, L2441–2631. **Status:** design agenda, **not** a claimed completed theory.

The source supplies an extensive vocabulary, but only some compositional laws. The following probes distinguish rival formalisms efficiently without presuming a single preferred abstraction.

| Unresolved question | Minimal discriminating probe | Implication of a positive or negative result |
|---|---|---|
| Do law changes form an operator action? | Choose two law changes and test associativity/composition and their action on system *morphisms*. | If no coherent operator algebra, index models by parameters/laws rather than forcing an actegory. |
| Can an internal partial action descend to the boundary? | Find two observationally equal states with different definedness or visible outputs. | A counterexample forces richer information-state or relational semantics. |
| Is restriction theory appropriate for this effect? | Test all four restriction axioms for the actual process category; start with nondeterministic branches. | If an axiom fails, do not export \(\bar f\) as a categorical enabledness operator. |
| Does abstract boundary behavior preserve composition? | Assemble two implementations with equal abstraction, including a feedback context. | A distinguishing context requires a finer behavior semantics or narrower allowed contexts. |
| Are component domains enough for global validity? | Keep domains fixed but vary emitted values so downstream preconditions differ. | Failure proves that interfaces need behavior/assumption transfer, not only predicates. |
| Is local solution consistency the real problem? | Construct local sections and test overlap agreement, gluing, and global boundary constraints separately. | Use sheaves only if this local/global mechanism is actually consumed. |
| Are singular solutions or gauge symmetries being lost? | Compare quotient points with different stabilizers or nontransverse constraint loci. | Preserve groupoid/derived data only where those distinctions affect judgments. |
| Does concurrency matter observationally? | Compare interleavings of independent events against a consumer sensitive to causal provenance. | If order/provenance matters, event structure or pomset semantics may outperform plain traces. |
| Do physical ports carry a compositional invariant? | Check power balance under actual interconnection and dissipation assumptions. | A verified energy balance supports Dirac/port-Hamiltonian structure. |
| Does replanning require an executable decision rule? | Present two hidden states with disjoint safe actions and one observation. | Statewise existence is not enough; a uniform observation-based policy is required. |

## Terminology left in reserve

**“Ehresmann spaces.”** The source supplies no precise object. Do not quietly interpret it as an Ehresmann connection, an Ehresmann category, or a differentiable space.

**“Kleisli bicategories of relations.”** Requires a declared base bicategory, higher monad/extension, 2-cells, and effect-composition laws; no unique construction is established by the chat.

**“Causal categories.”** Refers to multiple non-equivalent formalisms. Causal sites are one concrete example, not the canonical definition of every causal category.

**“Vary laws freely.”** Remains typed-hole terminology until allowed law changes, preserved interfaces, and admissible consumers are fixed. There is no meaningful theorem of free variation in a completely unspecified class.

## Next concrete theorem to try

Choose two finite-state components with partial commands and hidden state, let \(\mathsf W\) contain **serial and independent parallel** wiring but initially no instantaneous feedback, and choose external behaviors as history-indexed relations with explicit error outcomes. Define \(\beta\) and prove that it preserves serial and parallel assembly. Add one safety assume/guarantee contract, prove a compositional preservation rule with discharged assumptions, and find a counterexample when the compatibility premise is removed. Then introduce feedback and test whether the original behavior abstraction remains adequate.

This incremental target is deliberately much less general than the source's informal proposed “open restriction equipment.” It exposes the first genuine mathematical obligations rather than presuming the complete architecture exists.

**Related notes:** Note 20, Note 21.

---

## 23 — Other decomposition techniques in reserve

**Origin:** chat L665–693 and L918–946. **Status:** corrected short concept notes. These were mentioned but not developed far enough in the source to justify a detailed application claim.

These are retained because an eventual downstream problem may reveal their relevance. Their absence from the main architecture is **not** a proof of irrelevance.

| Technique | Formal cut worth retaining | Important limitation / discriminant |
|---|---|---|
| **Inverse/restriction inverse categories** | Partial arrows equipped with suitable partial inverses; categorical abstraction of partial isomorphisms. | A dynamical system that admits backward *solutions* need not be modeled by partial inverses if distinct states merge, stochasticity is present, or history is lost. |
| **Markov categories** | Symmetric monoidal categories with copy/discard structure for stochastic processes. | A conditional distribution or disintegration need not exist for arbitrary measure spaces. “Markov category” alone does not solve filtering or causal identification. |
| **Comonads and context-dependent updates** | Coeffects/local context may be expressed through comonadic structure; useful in cellular/context-sensitive settings. | A comonad is not generally an environment-dynamics operator action and does not supply a particular local-update law. |
| **Chu spaces** | Pair points/observations with an evaluation relation or pairing, often \((A,X,\langle-,-\rangle)\). | Structural point/test duality does not guarantee experiments distinguish physical states or provide a controller. |
| **Synthetic differential geometry** | Infinitesimal objects and internally formulated differentiation in a chosen smooth topos or related model. | Requires an ambient logic/model with appropriate infinitesimal axioms; not interchangeable with ordinary manifolds or an ODE solver. |
| **Cohesive toposes** | Adjoints/modalities separating shape, discrete, and codiscrete aspects of space in a cohesive setting. | “Cohesion” is not a generic physical coupling law or a flow semantics. |
| **Lie groupoids/algebroids** | Global symmetry/groupoid data versus infinitesimal anchored-bracket data. | A Lie algebroid need not integrate to an ordinary globally well-behaved groupoid; the integration and quotient questions are separate. |
| **Equipments/framed bicategories** | Distinguished vertical maps and horizontal proarrows with companion/conjoint-type structure where axioms hold. | Not every double category is an equipment; interface refinement versus behavior arrows requires a deliberate semantic assignment. |
| **Polycategories / linearly distributive categories** | Multiple-input/multiple-output composition with designated cut operations. | A symmetric monoidal category already has multi-port objects; extra polycategorical structure is justified only when the richer multicut behavior is actually consumed. |
| **Quantaloid enrichment** | Typed weighted relations with ordered-compositional semantics. | Requires specified hom-orders and composition; “reachability + cost + probability” is not one automatic enriched structure. |
| **Causal sites** | Two interacting region relations, e.g. containment and causal precedence. | Do not identify with event structures or claim causal order alone generates propagation laws. |
| **Hypergraph categories** | String-diagram wiring with special commutative Frobenius structure on objects. | A junction is not automatically physical equality, nondestructive copying, conservation, or a safe signal fan-out; semantics must be chosen. |

## Decision policy

Promote one of these candidates from reserve only after naming its **consumer** (a question, invariant, verification obligation, or assembly operator), its **additional preserved distinction**, and a **witness that a simpler model cannot answer the same question faithfully**. Otherwise it is a concept available for later search, not a proposed default framework.

**Related notes:** Note 03, Note 07, Note 10, Note 22.

---

## Finite verification record

These are bounded computational checks of **derived counterexamples** in the notes. They do not establish the general mathematical existence/composition theorems in the architecture proposal.

## Observation descent criterion (Note 09)

For \(S=\{0,1,2\}\), \(O=\{0,1\}\), with \(r(0)=r(1)=0\) and \(r(2)=1\), all 64 partial endomaps \(f:S\rightharpoonup S\) were enumerated. For each, all 9 candidate partial maps \(\hat f:O\rightharpoonup O\) were enumerated. An exact descent \(\hat f\circ r=r\circ f\) existed **if and only if** domain saturation and output consistency held. Exactly 24 of the 64 internal maps admitted descent. The mathematical iff proof is in Note 09; this computation is a finite check.

## Relational domain obstruction (Note 08)

For \(R(0)=\{0,1\}\) and \(g(0)=2\) with \(g\) undefined at 1, with the candidate restriction defined by the identity relation on existential domains, the two sides of the restriction axiom are:

\[
\bar g\circ R=\{(0,0)\},\qquad
R\circ\overline{g\circ R}=\{(0,0),(0,1)\}.
\]

They differ, disproving the proposed restriction structure on this relational interpretation.

## Two external law operator flows (Note 04)

Take \(V=\partial_x\), \(W=x\partial_y\), from \((x,y)=(1,4)\), \(t=3\), \(s=2\). Applying the \(V\)-flow then \(W\)-flow gives \((4,12)\). The opposite order gives \((4,6)\); their second coordinates differ by \(st=6\).

## Instantaneous feedback (Note 11)

For \(u\in\{0,1\}\), the equation \(u=1-u\) has no solution; \(u=u\) has two solutions. Used in \(F(*,u)=(u,h(u))\), these produce respectively no fixed-point feedback solution and two distinct external outputs.

## Scope of checks

The more substantial construction claims—typing a restriction-aware open-system category, obtaining a compatible feedback trace, lifting actions through law changes, and proving an assume/guarantee assembly theorem—remain **unproved design obligations**. The finite checks are diagnostic witnesses, not certificates for those ambitions.

---

## Technical references and verification scope

**Primary source for the notebook:** the conversation supplied by the user, `Pasted text(20261027-151133).txt`; note headers give the approximate chat-line origins. The links below are **external mathematical context**, used to check definitions or support explicitly expanded material—not evidence that the entire proposed heterogeneous open-system architecture has been constructed.

1. Capucci & Gavranović, *Actegories for the Working Amthematician*, [arXiv:2203.16351](https://arxiv.org/abs/2203.16351). Monoidal actions and coherent structures.
2. Cockett & Lack, *Restriction categories I: categories of partial maps*, [Theoretical Computer Science 270 (2002)](https://www.sciencedirect.com/science/article/pii/S0304397500003820). Restriction structure and partial map categories.
3. Cockett & Lack, *Restriction categories III: colimits, partial limits and extensivity*, [Cambridge Core](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/restriction-categories-iii-colimits-partial-limits-and-extensivity/DD7DED9C6268C85A27B26D9CCC468922). Splitting restriction idempotents and limits.
4. Goguen and collaborators, [Institutions](https://cseweb.ucsd.edu/~goguen/projs/inst.html); [Internet Encyclopedia of Philosophy](https://iep.utm.edu/insti-th/). Signatures, models, and satisfaction condition.
5. J. C. Willems, *The Behavioral Approach to Modeling and Control of Dynamical Systems*, [author-hosted/circulated PDF](https://citeseerx.ist.psu.edu/document?doi=12e43968c77466cfbd4720f2651220a9d7a5e365&repid=rep1&type=pdf). Behavior and control by interconnection.
6. Baez & Courser, *Structured Cospans*, [arXiv:1911.04630](https://arxiv.org/abs/1911.04630). Typed open systems by cospans.
7. Freyd–Scedrov-style allegory overview, [nLab: Allegory](https://ncatlab.org/nlab/show/allegory). Converse, meet, and modular law; consult primary monographs for theorem-level use.
8. Malherbe, Scott & Selinger, *Partially Traced Categories*, [arXiv:1107.3608](https://arxiv.org/abs/1107.3608). Extra trace structure and partial-trace axioms.
9. Winskel, *Event Structures*, [University of Cambridge technical report](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-95.html). Causality, conflicts, configurations.
10. Iglesias-Zemmour, *Diffeology*, [AMS](https://doi.org/10.1090/surv/185). Generalized smooth structures.
11. Kolář, Michor & Slovák, *Natural Operations in Differential Geometry*, [Weil-functor chapter](https://www.mat.univie.ac.at/~michor/kmsbookh.pdf). Weil algebras, tensor composition.
12. Ian Anderson, *The Variational Bicomplex*, [circulated monograph](https://ncatlab.org/nlab/files/AndersonVariationalBicomplex.pdf). Infinite jets and horizontal/vertical variational calculus.
13. van der Schaft, *Port-Hamiltonian Systems: an Introductory Survey*, [EMS Press](https://doi.org/10.4171/022-3/65); Cervera, van der Schaft & Baños, [Interconnection of port-Hamiltonian systems and composition of Dirac structures](https://www.sciencedirect.com/science/article/pii/S0005109806003682). Power-conserving interconnection and implicit systems.
14. Grabowska & Grabowski, *Tulczyjew Triples: From Statics to Field Theory*, [Journal of Geometric Mechanics](https://www.aimsciences.org/article/doi/10.3934/jgm.2013.5.445). Lagrangian/Hamiltonian presentations.
15. Ghani, Hedges, Winschel & Zahn, *Compositional Game Theory*, [University of Strathclyde record](https://strathprints.strath.ac.uk/64265/); Hedges, [Morphisms of Open Games](https://www.sciencedirect.com/science/article/pii/S1571066118300884). Open games and lenses.
16. Crainic & Fernandes, *Integrability of Lie Brackets*, [Annals of Mathematics](https://annals.math.princeton.edu/2003/157-2/p06). Obstructions to integrating Lie algebroids.
17. Brav, Bussi & Joyce, *A Darboux theorem for derived schemes with shifted symplectic structure*, [University of Oxford record](https://www.maths.ox.ac.uk/node/20137). One entry point for derived critical loci.
18. Tobias Fritz, *A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics*, [Advances in Mathematics](https://www.sciencedirect.com/science/article/pii/S0001870820302656). Markov categorical semantics.

**Scope limits:** The short notes on derived geometry, causal sites, coeffect semantics, polychannels, and arbitrary combined stochastic effects are **not full literature reviews**. The terms “Ehresmann spaces” and “Kleisli bicategories of relations” remain uninstantiated, as they were in the source. Only defined claims and scoped examples are retained.
