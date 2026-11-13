# Local operational certificates before global state reconstruction

Proof candidate, 29 October 2026. This is a separate synchronous operational witness calculus and an instance of the residual-certificate construction. It is NOT an interpretation theorem identifying its state-factor boundaries with the graph-vertex cuts of original C5, and does not prove original-envelope cell generation.

## Plain-language abstract

A proposed model can have exponentially many joint states even though each mechanism reads only a few variables. We need not build that whole state table before checking a proposed decomposition. Instead, this construction discovers bounded component groupings, local state descriptions and permitted messages together, then checks concrete equations over the variables each proposed mechanism actually uses. Those equations guarantee that the reconstructed components continue to implement the chosen model at every time step, including under feedback. Messages must be deliverable by the other components: an equation that secretly reads an inaccessible part of the environment is rejected. Different partial descriptions share the same unknown model, mechanisms and random sources. The construction retains every candidate consistent with the declared evidence and resource rules; it does not identify the actual physical environment merely because one candidate fits a finite readout record.

## 1. Declared universe and unknowns

Fix a finite budget of named state slots V, with finite nonempty alphabets X_v. A slot is a candidate latent coordinate, not a supplied physical component. Its name is retained across views and time only within a candidate world. A finite universe may also include finitely many alternatives for slot alphabets, sensor maps and alias alignments; a persistent selector chooses ONE such alternative for all its occurrences. Search over unbounded latent state dimension is not claimed.

Let U be a finite action alphabet, or a product of named action ports. Let Z be a finite product of named exogenous source alphabets. One source ID denotes one value z_s at an update, shared everywhere that ID occurs. For stochastic semantics, specify one law on this joint source vector, possibly with an explicitly finite persistent mode included among the state slots. The pathwise theorem below holds for every source sequence and therefore needs neither independence across components nor freshness in time. If an implementation instead uses independent fresh sources, that is an additional declared mechanism assumption, never an automatic consequence of factorization.

A candidate world theta selects, from finite libraries or unknown bounded table variables:

* a parent scope P_v for each state slot v;
* a transition table F_v:X_(P_v) x U_v x Z_(J_v) -> X_v;
* permitted observation tables H_c on specified scopes;
* source laws or source-law parameters where probabilities, rather than only support, are relevant;
* any persistent physical aliases or mechanism-table identities.

The whole update F_theta is defined coordinatewise by these tables. Dependence cycles are allowed: every F_v reads the OLD state. There are no instantaneous algebraic loops. The global carrier X=product_v X_v is mathematical notation; the algorithm need not enumerate its elements. Scope selection is unknown but bounded by the declared local libraries or budgets. Entries of one unknown table are shared wherever that table is used, including different observations, requested decompositions and time steps.

Finite readout records add explicit constraints: introduce x_v^t and z_s^t for latent states and sources; impose x_v^(t+1)=F_v(x_(P_v)^t,u^t,z_(J_v)^t) and H_c(x^t)=observed_c^t. These are local factors with actual time and source IDs. For noisy observations introduce their declared source variables as well. This is possible-world consistency, not a statistical confidence certificate. In particular, existence of one hidden trajectory is not proof that the candidate has the correct observation probabilities. Likelihood, calibrated confidence sets or probability-moment constraints, when wanted, require an additional justified evidence compiler.

## 2. Operational types and primitive witnesses

An open component type specifies finite owned state, named input/output ports, permitted source IDs, and a synchronous update/readout table. A wiring witness names each provider, encoder table, receiver and timing phase. It cannot create a source, a store, a sensor or an additional round of communication unless the declared library permits one.

The concrete operational constructors are:

1. **Local coordinate change:** a finite bijection q:X_S -> Y with its inverse d:Y -> X_S. The two inverse equations are checked on the local carriers.
2. **Assembly:** disjoint owned slot sets S_j partition a parent set S; component states are joined by their coordinate decoders, and declared wiring supplies their inputs from OLD component states and external ports. Shared source IDs remain shared.
3. **Task summary:** a possibly noninjective q:X_S -> Y, equipped with the local update and output equations below. This is an abstraction witness, not an exact concrete factorization.
4. **Interface adaptation:** an allowed finite encoder/adapter table with its declared read permissions and phase. Noninvertible adapters are allowed; their actual preimage alternatives are retained in certificates.

A concrete refinement is a finite diagram of these constructors with specified source/target mechanisms and actual coordinate/wiring tables. Equalities are extensional equalities of these finite maps, together with canonical tuple reassociation and the ordinary identity/composition laws. This is an explicitly semantic language of typed operational witness diagrams with finite primitive-table witnesses. Its admitted composites carry their computed resource types; an arbitrarily budget-truncated sublanguage is not asserted to be composition-closed or to form a virtual equipment. It is not the free original C5 presentation. The residual compiler can have both C5 and operational factors, but a connection between their meanings must be supplied, not inferred from the word "decomposition".

Empty owned blocks use the singleton state carrier. They still retain their input ports, source IDs and actual wiring constraints; zero owned state does not mean zero interface information. If a nullary construction is intended to use no state and no internal components, its declared interface map must be checked directly.

## 3. Local persistent realization equations

For each proposed component j choose an UNKNOWN bounded scope S_j, a state map q_j:X_(S_j)->Y_j, a declared input encoder e_j, and local mechanism G_j. The encoder's source-state support T_j, action support and allowed provider support are explicit. Its inputs at time t are old-state values, not future states.

Two sets of equations are required.

**Update equation:** for every assignment to the variables mentioned on either side,

    q_j((F_v(x,u,z))_(v in S_j))
      = G_j(q_j(x_(S_j)), e_j(x_(T_j),u), z_(J'_j)).       (U_j)

The left side uses every parent P_v needed to update S_j. The right side uses only the declared interface and source IDs. If G_j needs a source that j is not permitted to share, the typing/resource test rejects the candidate before checking equality.

**Delivered-interface equation:** when the input is to be supplied by the discovered components rather than an external sensor,

    e_j(x_(T_j),u)
      = W_j((q_k(x_(S_k)))_(k in Providers_j), u).         (W_j)

W_j denotes an actual permitted wiring circuit, not a freely chosen central table with access to all providers. For separated senders it factors through per-provider encoders W_(k->j), each reading only q_k and the actions/source ports available to that sender in its declared phase; named channels deliver their tuple, followed by permitted receiver postprocessing. Each constituent table and channel has its own timing, bit cardinality and read permissions. A joint encoder or central bus is allowed only if that is an explicit resource type. The displayed W_j is the composite denotation of that checked circuit. This equation is essential. Merely finding e_j that makes U_j true can hide all the original system in an inaccessible input port. External inputs are allowed only when they are named external channels in the model universe. A permitted message can depend on an action or a selector only if the declared timing makes that input available to its sender.

If the task observes tau(x,u), impose the explicit output equation

    tau(x,u) = D((q_j(x_(S_j)))_(j in TaskProviders),u).    (T)

This is tested over its true union of supports, which may be large. It is not a free oracle. Multiple task outputs can have separate local equations.

For an exact concrete decomposition, the S_j are disjoint and cover the parent owned slots, and q_j has an explicit local inverse d_j. For a task abstraction, overlapping or noninjective summaries may be allowed. The latter are not counted as independent physical stores or independent sources. If runtime storage of summaries is requested, its allocation and update implementation must be in the resource witness.

### Theorem 1  Local equations imply persistent realization

Suppose U_j and W_j hold for every j, and T holds for the requested outputs. For every root initial state x^0, every action sequence, and every source sequence, initialize y_j^0=q_j(x_(S_j)^0). The assembled component mechanisms then satisfy

    y_j^t = q_j(x_(S_j)^t)

at every time t, and reproduce the requested task output at every step. The assertion also holds for controllers whose action at time t is any function of the shared previous task transcript and their own fixed private state.

**Proof.** The induction hypothesis and W_j identify the delivered message with e_j evaluated at the actual old root state. Every occurrence of a source ID uses the same actual z_s^t. Equation U_j makes the next local state exactly q_j of the next root state. This proves the invariant simultaneously for all components despite recurrent dependencies, because all update reads are old-state reads. Equation T gives equality of task outputs. An adaptive controller receives the same past outputs in the coupled executions, hence chooses the same next action; induction continues. No independence assumption is used. Pushing the pathwise coupling through any common source law gives equality of the induced task transcript laws. QED.

For exact concrete decompositions, the product of the local inverse maps reconstructs x from y at each time. Every tuple of local states has one root state because the owned blocks partition a Cartesian carrier and each q_j is bijective. Thus the result is conjugacy of the full synchronous mechanism, with the same external actions and source record, not merely equality of a chosen finite readout sample. For task summaries, only the stated forward realization and task-output preservation follow; extra arbitrary initial summary tuples need not be realizable.

### Theorem 2  Exact local certificate compiler

For finite declared scopes, alphabets and table libraries, all clauses above compile to finite constraints over scope choices, ownership variables, table entries, source IDs, trace variables and endpoint pins. Enumerate each clause only over the UNION of the state/action/source coordinates it reads. Each satisfying assignment constructs the concrete operational witnesses and all-time realization of Theorem 1. Conversely, every realization witnessed by these local tables and full-carrier equations gives a satisfying assignment.

If X, U and Z have full Cartesian admissible domains and the claimed realization equation holds for every global state/action/source tuple, checking its local union support is also necessary: every local assignment extends to a global assignment. Thus there is no loss of completeness from replacing global identity checks by these local checks in this universe.

**Proof.** For each local assignment, table evaluation is a finite selector constraint. Unknown table entries are variables; one entry is not copied independently between clauses. Scope selectors can be represented by a disjunction over the finitely many permitted scopes. Ownership is a finite disjoint-cover constraint. Coordinate inverses are local table equations. Each constraint is exactly one finite instance of a stated requirement, not a query to an oracle deciding whole-system realization. Soundness follows from Theorem 1 and the constructor definitions. Completeness follows by inserting the actual tables of any witness in the declared universe. The Cartesian extension fact proves the last assertion. QED.

For non-Cartesian reachable state sets or state-dependent source supports, the unrestricted local equations remain sound but may be stronger than necessary. One may instead supply local invariant predicates and prove initial inclusion and preservation by analogous local implications. This is a different certificate universe: arbitrary reachable-state completeness is NOT claimed. Local projection membership alone does not establish that every locally allowed tuple extends to a reachable whole state.

## 4. Composition and crossing refinements

The same local mechanism variable is shared by every partial view that claims to describe it. Different decompositions have different ownership choices and state maps but one candidate world theta. To ask for a common refinement, introduce UNKNOWN cell ownership sets and component tables; require their row unions and column unions to equal the two parents' owned sets, and impose the appropriate local inverse/assembly and update/wiring equations at every parent. Shared cells have one mechanism, one source-ID assignment and one interface implementation. No common cell assignment or permissible interface is assumed to exist.

For concrete partition refinements, once parent ownership is fixed, set-theoretic intersections determine the only possible owned atoms of crossing cells. This alone does not give operational refinement: the cells may fail U_j or W_j, or require unavailable communication. This distinction is exercised by the selector interface stress family. If parent ownership is itself unresolved in the views, it remains a shared unknown during the solve.

Composition of two witnessed refinements is obtained by composing coordinate maps/decoders and composing the actual wiring tables where the declared timing permits it. Substituting the first update equation into the second proves the composite equation; identity witnesses are identity tables. Nested assembly is coherent by tuple flattening and finite function composition. However, a resource budget or a restricted message library need not be closed under arbitrary composition. The composed witness is admissible only if its resulting port/timing/resource type is admitted; otherwise the calculus records a typing obstruction rather than silently allocating resources.

Noninvertible interface changes are likewise checked on the particular witness. Forward postprocessing of a delivered message is always a defined table operation, but the new message may no longer suffice for U_j. Recovering a new local update table after such a change is a fresh finite constraint problem. Lifts use actual table preimages and preserve shared input IDs. No universal lifting or invertibility of interface transport is assumed or concluded.

## 5. Size and cost

Let ell be the largest number of finite-valued state/action/source coordinates in any single equation's true union support, and let a bound their alphabet sizes. For p local equations with fixed selected scopes, their truth-table expansion has at most O(p a^ell) assignment tests, multiplied by table-evaluation and encoding costs. Local inverse checks add the sizes of the local component carriers. If permitted scope choices are listed, expanding their alternatives adds their actual list sizes. A succinct family of exponentially many scopes does not have a polynomial expansion merely because each selected scope is small.

This can be exponentially smaller than enumerating all product_v |X_v| root states. It remains a strong structural regime: bounded owned blocks alone is insufficient if their transitions, providers or task outputs have large union support. The two-stage complexity is distinct:

* Construct and evaluate the local finite factors, charging O(p a^ell) or the heterogeneous support products.
* Solve the shared unknown-table/ownership constraints, charging their actual witness-factor width and domains through the residual algorithm. This can still be exponential or worse in the input parameters. No general efficient architecture search is claimed.

Checking one supplied local witness requires the same finite local identity checks, not rebuilding an exponential root transition table. An optional symbolic proof of a local identity can replace exhaustive truth tables, but its correctness and checker cost must be separately specified. Binary succinct state spaces, source laws and truth-table encodings are not free.

The output can preserve all readout-consistent candidate worlds as a constraint system rather than enumerate them. That is an exact compact specification, not a claim that querying every property of that family is cheap. Temporal observation factors may create high width even when the one-step mechanism neighborhoods are small.

## 6. What this adds and what it does not

Compared with the earlier operational recognizer, which starts from supplied whole finite state/event carriers, this compiler admits unknown local mechanisms, ownership and interface implementations before constructing the full product-state transition graph. Its persistent guarantee comes from proved local commuting equations and deliverable-interface equations, not from a whole-model equality oracle. The benefit is conditional on local representation and support bounds; the search complexity and model-universe dependence remain explicit.

This supplies a general operational instance of on-demand residual certificates. It does not identify unknown physical systems without restrictions, validate a model class from finite observations, prove a general stochastic identification theorem, or show that all operational witnesses are generated by original C5. A certificate for one possible model is not a guarantee for every model consistent with the data, and a family of model-specific implementations is not one uniform controller implementation. Those quantifiers must be requested and checked separately.
