# Safe discovery and mission completion with unknown sparse response interfaces

29 October 2026. Mathematical construction for a deterministic finite-memory subclass. This is not a theorem for arbitrary partially observed stochastic robots. Physical containment and timing remain separately supplied contracts. The standard mechanisms used below include version-space learning, knowledge-state reachability games, ranking certificates and finite constraint elimination; their combination is not by itself a novelty claim.

## Plain abstract

The question is no longer whether one supplied maneuver can stop. It is whether an agent can start with uncertainty, obtain useful information without leaving its safety envelope, and finish a task before its resources run out. We describe a class in which the relevant input histories and response interfaces are initially unknown. The agent learns only from allowed actions and delivered readouts. It retains every mechanism still consistent with those records, rather than pretending that a convenient explanation has been proved. A controller certificate must cover preparation, diagnostic actions, movement, termination and useful task completion. Safe refusal does not count as mission success.

The main construction uses joint diagnostics: a sensor can report the sum of two unknown response bits without revealing them separately. These observations create genuine correlations between persistent candidate mechanisms. A checked forest of acquired diagnostic constraints admits exact response-signature messages, which discover globally supported local response interfaces without enumerating the product of environment models. The relation is retained after local pruning; its marginals alone are not sufficient. Coordinate observations are a simpler special case. Tractability follows from the checked constraint structure and observation form, not from sparsity alone. A discovered interface exposes all remaining relevant history counters and their recursive updates. Local mission modules can be reused only when their assumptions, changed counters, retained knowledge and resource costs fit the next module. A decreasing rank proves completion only for initial knowledge states where a valid mission certificate is accepted. Starting from completely uninformative data need not be such a state: the class can contain environments with no feasible completing route. The safe end-to-end pipeline therefore performs bounded safe acquisition and either certifies a completing continuation using the actual remaining resources or safely abstains. Policy discovery can still be expensive; the theorem separates small model representation from potentially large policy search.

A companion obstruction explains why some missions cannot be solved: if every safe experiment leaves two goal-critical mechanisms indistinguishable, and they require incompatible commitments, no controller can guarantee completion. Thus safe information acquisition is part of the problem, not a free preliminary data source.

## 1. The implementation class and what is supplied

There are n binary control ports and m labeled response channels. A known upper bound L limits the relevant consecutive activation history. The public history interpreter maintains counters

    c_j in {0,...,L},
    c'_j = min(L,c_j+1) if a_j=1, and c'_j=0 if a_j=0.       (1)

One control word updates these counters once. A multi-tick maneuver must specify its actual sequence of control words and update them at every tick; it cannot silently count as one history update. The initial counters must be obtained from a sound initial-state claim or an executed, physically safe synchronizing sequence. For (1), a delivered all-zero word synchronizes counters to zero if all relevant ports can actually be set to zero. If such a command is unavailable or unsafe, this synchronization is not licensed. A longer claimed flush is charged in full and must have a proof for the actual update law.

The response on channel i is an unknown fixed function f_i(c). The supplied function universe H contains:

- the two constants;
- either polarity of a threshold 1[c_j >= ell], for an unknown j and ell in {1,...,L};
- an arbitrary Boolean function essential in both of two threshold predicates on distinct unknown ports.

The actual ports, thresholds and Boolean tables are not supplied to the learner. After canonical removal of dummy variables, the catalogue has

    M = 2 + 2 n L + 10 binom(n,2) L^2                     (2)

functions. There are 10 Boolean functions depending essentially on both arguments: of the 16 binary truth tables, two are constant and four depend on only one argument. Port indices are sorted so swapping argument names does not duplicate the same function. The catalogue is a local structural universe, not a supplied list of whole environments. A complete mechanism is theta=(f_1,...,f_m), with M^m possible tuples before data.

This family supplies the run-counter form and the width-two upper bound. It discovers which counters, thresholds and Boolean interactions are needed, not an arbitrary hidden-state realization. The case is deliberately noiseless: delivered response bits are exact evaluations. Noise, drift, unmodeled common modes and arbitrary rare hazards are not learned away by finite consistency checks.

The mission also has public state s: location/bay, payload or task-progress flags, available energy, elapsed time and other explicitly represented variables. The physical contract supplies the permitted controls and sensors at each location, known coarse-safe maneuvers, the meanings of guard responses, segment-duration/resource bounds, and a sound initial safe set. Unknown f_i determine when the improved local physical envelopes apply. The response-to-physics interpretation is supplied calibration, not a conclusion of Boolean-function discovery.

The mechanism tuple theta is chosen once and remains fixed. Sharing an input counter creates an interaction between response interfaces, but does not imply a shared hidden parameter. The product universe H^m is a substantive premise. If mechanisms obey additional correlated restrictions or share an unobserved mode, that relation must be represented; the product theorem below does not apply automatically.

## 2. Actual records, exact persistent uncertainty, and adaptive acquisition

A retained diagnostic record is (c,i,y): at the known counter state c, the permitted sensor delivered f_i(c)=y. The observation protocol may reveal several individually labeled channels in one operation. The main extension below also permits known pair-sum diagnostics, with their coherent relational constraints retained. Actions may be selected adaptively from all earlier permitted records.

Let D_i be the records retained for channel i and define

    H_i(D_i) = { f in H : f(c)=y for every (c,i,y) in D_i }.

The controller stores the local sets H_i, known counters and public mission state. Empty H_i is a model-consistency failure, not permission to choose an arbitrary replacement model. Such failure must terminate under the independently safe physical fallback, and does not count as successful completion.

### Theorem 1: exact product knowledge under coordinate observations

Assume the initial possible-mechanism set is H^m, the retained observations are individually labeled exact responses, and all public-state transitions delivered to the controller are either mechanism-independent or already guaranteed identical by the admitted physical contract. Conditional on any finite executable retained transcript h, the set of fixed mechanisms consistent with h is exactly

    K(h) = product_i H_i(D_i(h)).                          (3)

This remains true when the controller chooses diagnostic actions, sensor subsets and stopping times adaptively. No independence assumption about successive records or concentration inequality is needed.

**Proof.** Initially the claim is the class premise. Fix a transcript prefix and the controller's random seed, if it uses independent randomization. The selected next action is a function of the existing transcript and seed; conditioning on that action adds no constraint on theta beyond the existing transcript. The current counter state is known from the actual control history. Revealing channel i with result y intersects K with the cylinder {theta:f_i(c)=y}. Intersecting a Cartesian product with one such cylinder changes only its i-th factor. Several individually identified responses impose several such cylinders. Public mechanism-independent outcomes add no further constraint. Induction proves (3). Conversely every tuple in the resulting product reproduces the retained transcript under the same adaptive action choices, because it satisfies each response constraint and the public transitions agree. QED.

The theorem concerns the retained evidence interface. A controller may deliberately ignore extra physical side channels, but then (3) is a conservative representation of its richer actual knowledge, not a claim that those side channels carry no information. Such information asymmetry must be kept fair in comparisons.

**Why sparsity alone is insufficient.** Let two independent unknown constant responses be theta_1 and theta_2. An aggregate observation theta_1 XOR theta_2=0 changes their joint possibility set to {(0,0),(1,1)}. Each marginal remains {0,1}; their product adds the impossible pairs (0,1) and (1,0). A sparse system has therefore acquired a non-product knowledge relation in one observation. If such observations are used, retain their relational factor, and charge inference width. Dropping the factor is at best a conservative overapproximation for universal safety and can destroy valid progress; choosing inconsistent favorable marginals is unsound.

## 2A. Main relational extension: discovering globally supported interfaces from joint diagnostics

A pair diagnostic on channels i and j at known counter state c returns

    s = f_i(c) + f_j(c), in {0,1,2}.                      (8)

Different endpoint contexts c_i,c_j are also allowed if the sensor protocol certifies their timestamps and retains both known states. The returned sum is a known sensor interpretation; neither constituent response is supplied. Repeated diagnostics produce records r=(i,j,c_i^r,c_j^r,s_r). Coordinate observations remain unary constraints. The actual tuple theta stays fixed during all observations.

Let H_i contain the local catalogue after unary filtering. For each acquired pair e={i,j}, define

    C_e(f_i,f_j) iff, for every record r on e,
                       f_i(c_i^r)+f_j(c_j^r)=s_r.

The exact persistent uncertainty is the relation

    K_D = {theta in product_i H_i : all C_e hold}.         (9)

The proof is the same transcript-consistency induction as Theorem 1, except each new observation intersects with a two-coordinate cylinder instead of a one-coordinate cylinder. Adaptively choosing the next diagnostic adds no evidence beyond its recorded outcome. Thus these are actual acquired constraints on unknown mechanisms, not a supplied hidden factor graph. The graph of *observed constraints* is known from the sensor operations; it is distinct from the unknown response-to-input dependency graph that discovery aims to recover.

Assume first that the acquired diagnostic graph is a forest. This is a directly checkable property of records. It is not inferred from width-two response functions. If a new diagnostic creates a cycle, the forest algorithm below must not be used as an exact solver: use a separately checked tree decomposition, or retain an explicit unresolved inference obligation. A planner may choose to preserve a forest, but the safety and completion theorem does not assert that a sufficient diagnostic forest always exists.

For an oriented edge i -> j, remove e from the forest and call the i-side subtree T_i. Define the Boolean separator message

    M_{i->j}(f_j) = 1 iff there exists a choice of every
    mechanism on T_i satisfying its unary constraints,
    all internal acquired pair constraints, and C_e.

The message is indexed by the persistent function f_j, not by an independently reselected output bit. A function must satisfy all its incident diagnostic records simultaneously.

### Theorem 1R: exact signature-message discovery on a diagnostic forest

All separator messages, the consistency of K_D, and every exact local projection P_i=projection_i K_D can be computed without enumerating the product of local hypothesis sets. For edge e with k_e records, define the response signature

    sigma_{i,e}(f_i) = (f_i(c_i^r)) over records r on e.

Given all incoming messages to i except that from j, retain

    A_{i|j} = {f_i in H_i : M_{k->i}(f_i)=1
                              for all neighbors k != j}.

Hash the signatures sigma_{i,e}(f_i) of functions in A_{i|j}. Then

    M_{i->j}(f_j)=1 iff s_e-sigma_{j,e}(f_j)
                   is a binary vector occurring in that hash set. (10)

A postorder pass and a preorder pass compute all messages. First test every connected component for consistency, for example by asking whether its root has any value allowed by all incoming messages. If any component is inconsistent then K_D is empty and every global projection is empty. Otherwise the exact projection at node i is

    P_i = {f_i in H_i : all incoming M_{j->i}(f_i)=1}.      (11)

If K_D is nonempty, replacing H_i by P_i while retaining every C_e preserves K_D exactly. Replacing K_D by the product of P_i generally does not.

**Proof.** In a leaf-to-parent message, compatibility with e is exactly the coordinatewise sum condition, which is equivalent to the signature complement test. For an internal node, deleting its parent edge makes its child subtrees disjoint. Once f_i is fixed, each child subtree has a compatible assignment iff its incoming message permits f_i. Those assignments share no remaining variables and can therefore be joined. This proves the message recurrence by induction on subtree size. The second pass applies the same argument to the reverse orientations. Removing all edges at i partitions its component into independent subtrees conditional on its one fixed f_i; hence their messages are jointly sufficient and necessary for a compatible component assignment. When every other component is consistent, these assignments join to a full assignment, proving (11). If any component is inconsistent, no global assignment exists and all projections are empty. Every full assignment already uses values in each exact projection, so pruning them preserves the relation. Marginal products need not preserve edge constraints, as shown below. QED.

The hash construction evaluates signatures in O(k_e(|H_i|+|H_j|)) time per oriented edge, using exact binary strings, rather than explicitly materializing the |H_i| times |H_j| relation. Accounting for exclusion of one incoming edge by prefix/suffix Boolean conjunctions, both passes cost

    O(sum_i (1+degree(i))|H_i| +
      sum_e k_e(|H_i|+|H_j|))                            (12)

hypothesis/bit operations up to hashing overhead and evaluation of the declared local functions. Hash collisions must be resolved by exact signature equality. Storage is O(sum_i (1+degree(i))|H_i| + sum_e k_e(|H_i|+|H_j|)) if signatures are cached, or they may be recomputed with time/storage tradeoff. These are explicit polynomial costs in the local catalogue and records, not in M^m. Repeating the passes after each new record is valid; incremental caching is optional and its real cost must be reported.

**Coherent witness reconstruction.** Store one admissible child function for each hashed signature in (10). For any selected globally supported root function, choose compatible child representatives and recurse, using the incoming-message restrictions already included in each child hash. This constructs one full mechanism tuple satisfying every acquired record, without a Cartesian-product search. A proposed unsafe joint query can similarly return one globally coherent counterexample by backtracking an exact augmented-query elimination. Such a witness demonstrates compatibility with the records, not identification of the true mechanism. Choosing one separately supported function per node without this backtracking would not be valid.

This is an application of exact acyclic constraint propagation and hash joins. The useful specialized result is that a learned response-function domain and repeated aggregate diagnostics admit the compact signature relation (10). The general semijoin/tree-message principle is established machinery, not a new general inference algorithm.

### Why the relation can matter to mission completion

One pair-sum observation equal to 1 gives the alternatives (0,1) or (1,0) at that context. Both individual projections are {0,1}, yet the joint relation proves that at least one response is 1. A mission may need to establish this before entering a resource-limited region, then obtain a permitted local observation inside to select the feasible exit. The product of marginals introduces the impossible both-zero world and can wrongly declare that mission impossible. Conversely independently choosing favorable marginals could admit the impossible both-one world and unsoundly justify an action that needs both. The exact relation supports either existential or universal queries only with coherent assignments.

The gain must be demonstrated with actual access restrictions, timing and physical witnesses; this logical example alone is not a robot experiment. Nor does it establish that true mechanism identification is necessary: mission-relevant relational knowledge can suffice while many local functions remain possible.

### Discovery and queries after relational propagation

Use the exact projections P_i, not merely unary H_i, when reporting globally supported scopes and constructing local observers. Apply the essential-variable and threshold rules below to every f_i in P_i. This discovers the response interfaces compatible with the complete acquired evidence, including constraints arriving from distant diagnostics. The acquired diagnostic graph itself is not claimed to be the physical decomposition; it is the certificate structure used to infer the unknown response interfaces.

A single-response support query is immediate from P_i. A joint query cannot independently multiply these projections. To check that every theta in K_D satisfies a mission condition F((f_i(c))_{i in I}), ask whether

    K_D AND NOT F((f_i(c))_{i in I})                       (13)

is satisfiable. If I lies in one diagnostic edge, the signature message machinery can be extended to filter that edge or enumerate its compatible endpoint signatures. A general F introduces an additional query factor; its induced width and factor-description/evaluation cost must be charged. A tree diagnostic graph does not guarantee that every arbitrary mission query remains tree-shaped. For a supplied and checked tree decomposition of the augmented query graph of width tau, ordinary exact elimination costs O(poly(m,record size) M^(tau+1)). Do not claim this for an unverified bounded width.

### Persistent successor relation

A new pair diagnostic has at most three outcomes. An outcome is realizable exactly when adding its factor leaves (9) satisfiable. Keep only those branches, and retain the added constraint permanently. Coordinate observations filter a unary domain. Public action/counter/resource updates remain as before. Along a finite branch, all acquired constraints are conjoined on the SAME f_i variables. Any assignment of the final nonempty K_D therefore reproduces every earlier response. This is the relational extension of Lemma 4: exact adaptive branching preserves persistent mechanisms without enumerating them.

## 3. Discovery outputs an executable interface, not a guessed true model

In the product special case let P_i=H_i; in the main relational case compute the exact projection P_i using Theorem 1R or another exact inference method. At a particular counter state, the sound possible-response set is

    V_i(c,P_i) = { f(c) : f in P_i }.                      (4)

A response is certified to be 1 only when V_i={1}. When V_i={0,1}, uncertainty remains. The learner is not required to identify an entire f_i before making a task-relevant decision. Different functions can agree on every query needed by a mission, while disagreeing elsewhere.

For an unambiguous discovered scope claim, first remove constants, dummy arguments and syntactic aliases. If every surviving candidate is the same function on the full declared counter domain, its essential ports and thresholds are identified within this class. Otherwise report the surviving alternative scopes or their conservative union, not the simulator's true scope. Two width-two candidates can be compared on the union of their at-most-four ports; no n-counter product enumeration is needed. A brute-force equivalence test uses at most (L+1)^4 evaluations per pair, and the canonical catalogue above avoids most such comparisons.

Define R_i to be the union of essential input ports of globally supported candidates in P_i. For j in R_i let

    ell_ij = max {threshold on j in an essential occurrence
                  in any f in P_i}.

The discovered local observer for response i stores

    q_ij = min(c_j,ell_ij), for j in R_i.                  (5)

### Lemma 2: recursive sufficiency of the discovered observer

Every f in P_i can be evaluated from q_i. Its update under each delivered control word is recursive: q'_ij=0 for a_j=0 and min(ell_ij,q_ij+1) for a_j=1. If later evidence removes candidates, a smaller observer is initialized by truncating or projecting the existing observer. No hidden counter value is needed.

**Proof.** Every used threshold ell is at most ell_ij, so c_j>=ell iff min(c_j,ell_ij)>=ell. Truncation commutes with the increment-and-cap update in (1), and with reset to zero. New maxima never increase when P_i shrinks, so the smaller state is a projection. QED.

This is useful memory discovery inside the supplied counter grammar. It is not discovery of the grammar itself. Mission feasibility, actuator cooldown or physical monitoring may require counters beyond (5); those must remain in the combined implementation. Predictive memory savings are not automatically total-controller memory savings.

The interface also retains the persistent hypothesis identifiers and diagnostic relation needed by joint mission queries. The interface names every counter provider and response consumer. Responses sharing counters overlap semantically; the counter is updated once by the actual controls and its projections are shared consistently. Independently inventing local counter histories is forbidden. Connected components of the discovered response/input incidence graph can organize reusable response modules, but are not claimed to be independent physical robots: common position, energy, time, actuation and mission obligations still couple their use.

In the coordinate-observation special case, discovery storage is O(mM+n) hypothesis identifiers/counters before optional compression. Processing a coordinate record on channels O costs O(sum_{i in O}|H_i|) evaluations. Separate single-response support queries on I cost O(sum_{i in I}|H_i|). The main aggregate case additionally stores acquired relational records and pays the signature/message costs of (12); joint queries pay their exact augmented-query cost in (13). The input labels and control words themselves cost O(n), and counter-provider communication is charged by the actual interface graph. These costs avoid M^m environment enumeration; they do not imply that mission-policy search is polynomial.

## 4. A more general sparse-record discovery lemma

The preceding parametric catalogue is not the only permitted discovery route. Suppose a deterministic output has the form y_i=f_i(x[T_i]), with unknown port scope |T_i|<=w and known finite observable-history dictionary x. A candidate scope U, |U|<=w, is consistent when all records with the same x[U] have the same output. Its partial table g_U is then defined on observed U-rows.

For a proposed query x, define a union-scope coverage gate: for every V with |V|<=w, at least one actual record has the same restriction x[U union V]. This gate uses recorded local projections, not simulator access to T_i.

### Lemma 3: safe use of a locally consistent table

If the true scope is in the supplied class, U is consistent and the query passes the union-scope gate, then g_U(x[U])=f_i(x[T_i]).

**Proof.** Set V=T_i in the gate. A matching actual record has the same true-scope input and therefore output f_i(x[T_i]); it also has candidate row x[U], whose observed output equals g_U(x[U]) by consistency. QED.

The raw records may be sequential, adaptive and highly dependent: the proof is deterministic. It does not license the predecessor project's statistical concentration formulae for independent reset endpoints. A sparse projected table can be stored without enumerating the global history product, but the number of local rows, the search over scopes, and the physically safe cost of acquiring matching records must all be charged. The gate may reject the desired query because no safe experiment can obtain its required evidence. Lemma 3 is not a reachability theorem for those probes.

For a finite suffix dictionary, a totalized local table can be minimized by stable Moore-machine partition refinement, preserving unknown-row sentinels and recursive updates. A raw-history coverage monitor remains separately charged. The counter subclass in Lemma 2 admits the simpler explicit recursive observer.

## 5. Physical segment contracts and mission semantics

For each public state/counter/knowledge configuration k=(s,c,K_D), with K_D stored as local candidate domains plus retained relational factors, the controller proposes an allowed action a. The action can be a diagnostic pulse, a coarse-safe transport, a guarded traversal, a task operation, or a final stop. Its physical contract identifies:

1. a certified initial physical set U(k);
2. the actual control sequence and readout permissions;
3. the guard-response queries or other envelope conditions on which safety depends;
4. a bound covering the whole segment, including communication, computation, actuator response and any stopping tail;
5. all possible declared outcomes, their counter/public-state updates, and conservative energy/time costs;
6. the certified endpoint set U(k') or a safe terminal set.

Let G be the event that these supplied physical contracts and sensor interpretations are valid throughout the mission. On G, an admitted segment must be collision-free for every fixed theta in K(k), and every permitted physical outcome, and must reach the declared successor endpoint. The action is chosen before any new response is revealed. A later successful diagnosis cannot retrospectively justify an unsafe preparatory action.

A diagnostic bay is not an information oracle. Its physical invariant must show that the allowed pulses, including every intermediate counter state and their timing, remain safe. Access restrictions determine which controls and sensors are actually usable there. Travel to the bay and all diagnostic costs belong to the mission. No free reset, unseen mode read, omitted warmup or uncharged failed attempt is allowed.

A successful terminal state means the declared useful task is complete, the deadline and energy constraints are met, and the vehicle has reached the appropriate safe terminal physical set. Safe abort, refusal to move, timeout, consistency failure and stopping short of delivery are not goal states. They may preserve physical safety but fail this completion claim.

If physical validity is only probabilistic, with P_theta(G^c)<=eta_phys uniformly over the admitted controllers, a support-safe mission proof establishes both

    P(collision) <= eta_phys,
    P(success) >= 1-eta_phys,                             (6)

provided success on G includes all physical/resource/timing conditions. Eta_phys is an external unmeasured allowance unless actual calibration establishes it. In the synthetic model G can hold by construction; that is not evidence that a real device has eta_phys=0.

## 6. Persistent-knowledge mission synthesis

For the main aggregate-observation class, use the persistent successor relation in Section 2A and exact realizability queries; do not replace it with marginal Cartesian products. For the coordinate-observation special case, the exact successor calculation is explicit. Apply the actual control sequence, obtaining known new counters c'. For each revealed channel i, possible outputs are V_i(c',H_i). Since K is the product in (3), every vector in the Cartesian product of these sets has a compatible fixed mechanism tuple. Following output y_i, replace H_i by {f in H_i:f(c')=y_i}; leave unobserved H_j unchanged. Empty-result branches are impossible and must not be created. Update public state, resources and task progress through the admitted physical contract.

For more general observations, use a relation K(theta,x) including latent physical state x and persistent theta. The successor is relational image followed by restriction to the actual observation; theta is never freshly selected or forgotten. A local-factor implementation is possible, but its induced width can grow with conditioning and is not bounded by response sparsity alone.

### Lemma 4: support branching preserves persistence

For a finite response-observation tree with the exact update above and nonempty knowledge at every node, all response constraints on every root-to-leaf branch are jointly realizable by one fixed initial mechanism tuple. In particular, the response tree does not give an adversary permission to change f_i between observations. A physical transition abstraction may independently overapproximate realizable trajectories; this lemma does not turn every abstract physical branch into a realizable plant trajectory.

**Proof.** Along a branch each H_i only shrinks, and every update retains a nonempty set. At the final node choose any f_i from its surviving H_i. This f_i satisfies every response constraint accumulated on the branch. The tuple therefore reproduces every recorded response observation and the adaptive control choices given the declared public branch. The lemma makes no additional assertion that a conservative physical abstraction's public branch is exactly realizable. QED.

For probabilistic transition laws, arbitrary support-adversarial branching is generally stronger than a fixed-model probability bound and is not an exact stochastic optimizer. Lemma 4 is an exact realizability statement for this deterministic fixed-mechanism subclass. A shield that replaces H_i by its initial marginal set at every time, or forgets correlation factors in a relational K, uses a different and possibly much more conservative game.

### Theorem 5: sound mission-completion certificate

A finite controller certificate consists of nodes q, each labeled by public controller information k(q), an action at nonterminal nodes, all realizable delivered-outcome successor edges, and a nonnegative integer rank r(q). It must satisfy:

- the root's U(k) contains every permitted physical initial state, its knowledge contains every permitted initial mechanism, and any synchronization/acquisition prefix is part of this graph;
- every terminal node is a useful safe mission goal as defined above;
- every nonterminal action respects control/sensor permissions and the universal physical segment contract for its knowledge relation;
- all realizable successors appear, have sound updated knowledge/public state and certified endpoint sets, and satisfy r(q')<r(q);
- nonterminal nodes have at least one realizable successor; no abort/deadline violation is silently relabeled goal.

Then, on G, executing the certificate from its declared initial state is collision-free and reaches a useful safe goal after at most r(q0) actions. The same conclusion holds for every fixed mechanism in the initial class, including ones never uniquely identified.

**Proof.** True-mechanism containment follows by induction from consistency filtering or exact relational update. The physical segment contract therefore applies to the true mechanism at each action and preserves collision freedom and endpoint containment. Every realized outcome has a represented successor. Strict rank descent excludes an infinite execution and bounds the number of nonterminal transitions. A finite maximal run cannot end at a nonterminal node because the true mechanism supplies a realizable successor; hence it ends at a terminal goal. Resource and timing validity are part of the node and segment obligations. QED.

A physically safe fallback is useful operationally, but adding it as a non-goal terminal does not satisfy this theorem. If a practical policy has such leaves, report a weaker completion claim rather than discarding those branches.

With a finite resource-bounded public state space, define W_0 to be goals and

    W_{r+1} = W_r union {k: some permitted sound safe action
                         has a nonempty set of allowed abstract successors,
                         all in W_r, and nonempty K_D}.             (7)

Treat physically conservative but response-consistent successors as adversarial abstract outcomes even when their exact physical realizability is not established. Then the root is in union_r W_r exactly when a finite bounded-action universally successful policy exists in this abstract class. Membership constructs the rank certificate. Conversely a certificate of rank r implies membership in W_r by induction. This completeness is with respect to the supplied physical abstraction, action library and observation protocol, not all physically possible controls. The attractor construction is standard knowledge-game synthesis and can be exponentially large.

## 6A. Selective end-to-end assurance from initially empty evidence

Theorem 5 is a verification implication: IF a rank certificate passes at a declared initial knowledge state, THEN every retained mechanism has a safe completing continuation. It does not say such a certificate exists for every initial state, or even for the completely uninformed class H^m. In particular H contains the constant-zero response. If every useful route needs a positive guard and the coarse alternative misses the fixed deadline, the all-zero tuple is in the initial class but has no successful mission. No sound algorithm can guarantee completion for all initial hypotheses in that instance.

The useful weaker statement must join safe acquisition to conditional acceptance without pretending acquisition was a free supplied history.

### Theorem 5S: safe acquisition followed by certified completion or safe abstention

Suppose the actual fixed mechanism belongs to K_0 and the following conditions hold.

1. A declared acquisition controller A starts in a physically justified state. For every mechanism in K_0 and every delivered response prefix, each acquisition action satisfies a physical segment witness covering its whole duration. Its exact evidence update retains the true mechanism. Every acquisition endpoint has an independently justified safe-abstention continuation.
2. Acquisition terminates after at most B_A executed actions or time units, as specified, using an explicit stopping rule or rank. Budget exhaustion, empty evidence, unsupported scope/graph shape, inference failure and search timeout lead to the safe-abstention continuation. Runtime exceptions alone are not a demonstrated implementation of that continuation.
3. At termination time tau, the verifier reads the ACTUALLY acquired K_tau, counter state, location, task state and consumed resources. It either rejects, or accepts a Theorem 5 continuation certificate from precisely that state. All continuation and final-stop costs fit the remaining predeclared mission budgets. Certificate-search computation is included whenever it consumes modeled time or energy; offline uncharged proof work is not silently an online deadline claim.
4. The program executes a verified certificate on acceptance, and otherwise executes the certified safe-abstention continuation. Safe abstention does not count as useful completion.

Let A_c denote the event that this actual acquisition produces an accepted continuation certificate. On the physical-contract event G, the entire execution from the original initial state is safe for every theta in K_0, and A_c implies useful completion within the declared budgets. For this specific program, if acquisition itself does not deliver the goal and rejected branches always abstain, useful completion on G occurs exactly on accepted branches. This is NOT an equivalence between acceptance and the existence of some feasible physical mission policy: a limited proposer or conservative abstraction can reject a solvable case.

**Proof.** Induct over the finite acquisition execution using its universal physical witnesses. Exact evidence restriction never removes the true mechanism; all actual time/energy/counter changes remain in the reached state. On rejection, the safe-abstention witness completes a safe terminal execution. On acceptance, that reached state satisfies the checked continuation precondition, so Theorem 5 supplies safe goal-reaching execution with the remaining resources. Concatenation covers every preparatory, diagnostic and movement segment as well as the stopping tail. QED.

If physical-premise failure is bounded by eta_phys, then

    P(collision) <= eta_phys,
    P(success) >= P(A_c) - eta_phys.                      (14)

No positive lower bound on P(A_c) follows from the theorem. With no distribution on initial mechanisms, the meaningful statement is the mechanism-wise conditional implication, not an invented acceptance frequency or average success guarantee. If eta_phys is unmeasured, these remain conditional formulas.

**Additional premise needed for initial universal completion.** A sufficient stronger assumption is that the original knowledge/resource state belongs to the winning set (7), together with a complete synthesizer that actually finds its policy within the charged computational budget. Equivalently, one may supply a safe finite acquisition policy whose EVERY possible terminal transcript admits a verified completing continuation within the same original budgets. These are substantive safe distinguishability/viability premises. Merely exhibiting one favorable acquired transcript, or checking both outcomes of a final diagnostic after an earlier favorable transcript, does not establish them.

**How to describe the constructed experiment.** An executed commissioning trace from unknown history is stronger than handing the controller a favorable initialized state. All its costs and safety must be counted. However, a constructed world that yields useful learned scopes and a completing continuation establishes only that acquired branch unless the whole pre-acquisition policy tree is certified. Checking all remaining final-diagnostic branches proves robustness to the uncertainty still present there, not to every originally possible mechanism. Failed shape checks or unavailable certificates require safe abstention for the total program.

A deadline set to `actual commissioning time + service allowance` defines a paid commissioning phase followed by a service-window requirement. It is not a fixed absolute launch-to-delivery deadline. For the latter, declare the overall budget before observing acquisition outcomes and use its actual residual at acceptance; alternatively use a proved a priori worst-case acquisition bound. Either convention is legitimate if stated, but they must not be interchanged in a claimed comparison.

## 7. Safe distinguishability and genuine impossibility

Equation (7) gives an exact obstruction when its finite state space is explicitly computed: a root outside the winning set has no universally successful policy in the declared abstraction. Merely failing to find a policy within a search budget is not this proof.

A smaller information-theoretic obstruction is often more revealing. Suppose two fixed mechanisms theta and theta' remain compatible at an initial state. Until a commitment is made, every action safe for both produces the same delivered observation and public transition in both worlds. Suppose every useful completion must eventually make a first commitment, and no commitment enabled after such a common safe history both remains safe and permits completion in both worlds. Then no observation-based controller can guarantee safe completion in both worlds.

**Proof.** Couple any controller's internal random seed between the two worlds. Inductively, all safe precommitment histories and actions are identical. If it never commits, useful completion fails. At the first commitment it chooses the same action in both worlds, contradicting the stipulated absence of a jointly safe completing commitment. A randomized controller cannot obtain probability-one safety and success in both by mixing incompatible commitments: every commitment with positive selection probability fails in at least one world. QED.

The condition concerns all common-safe observation histories, not merely one failed diagnostic. It is stronger than having two different true models: different models can still admit a common safe mission policy. Conversely, inability to identify the entire environment is not an obstruction when its unresolved distinctions are irrelevant to the mission.

A small canonical example is a fork with one unknown persistent bit. Left succeeds only for bit 0, right only for bit 1, and the wrong commitment is unsafe. Every safely accessible diagnostic returns the same symbol in both worlds. Staying at the fork is safe but not completion. Adding a safely reachable distinguishing measurement changes the problem; allowing an unsafe probe does not solve the original safe mission.

## 8. Reusable local mission contracts with a frame condition

A learned response interface is not by itself a reusable mission controller. A local mission module includes:

- named response hypotheses and history-counter providers it reads;
- controls/counters, public state and hypothesis sets it can change;
- a precondition describing required knowledge, physical endpoint, task state and resources;
- a finite policy/rank certificate and a set of outcome-dependent postconditions;
- segment witnesses and conservative time/energy costs;
- a frame describing unchanged knowledge and any shared state that must persist.

The same mechanism identities and counter histories must be retained across module boundaries. A module cannot switch to a different favorable candidate on entry. A pulse that changes a counter used by a later module must expose that changed counter, even if the present module's own response does not use it. An unobserved response's candidate set remains unchanged under product coordinate observations; its relevant counter state may nevertheless change. In the relational case, new evidence on another channel can change its globally supported projection through separator messages. A module must therefore retain the full relation or a sound exact separator summary on its boundary; it cannot freeze an old marginal and call the components independent. Eliminating internal mechanism variables is valid only for later queries confined to the retained boundary. If a later module may reactivate those variables or observe their responses, preserve the eliminated factors and identities for exact rejoining; a boundary marginal alone cannot reconstruct the lost conditional relation.

### Theorem 6: compositional mission reuse

Take a finite acyclic mission skeleton whose nodes invoke verified local modules. At every edge, require each possible postcondition of the preceding module, including its updated knowledge, counters, physical endpoint and resources, to imply the next module's precondition after the declared shared-state wiring. Require every final postcondition to satisfy the global mission goal. Then the composed controller satisfies Theorem 5. The modules may have been learned and verified before this particular mission ordering was requested.

**Proof.** True-mechanism containment and physical endpoint containment are preserved inside each module. The implication and frame checks establish the next module's assumptions using the same persistent mechanism/history. Induction along the acyclic skeleton gives safe execution and a goal at every final leaf. A global rank can use a lexicographic pair: the remaining topological level of the acyclic skeleton, followed by the current module's local rank. Within a module the latter decreases; at a module edge the former strictly decreases. If local ranks are at most R, encoding the pair as (R+1) times the topological level plus the local rank gives a natural-number rank. Zero-step modules can be collapsed. Alternatively use maximum remaining path costs when summing local step bounds across branching skeletons. QED.

For cyclic mission skeletons, safe local modules alone do not prove completion. Supply a separate well-founded mission rank that decreases across cycles, or a genuinely stochastic termination argument with its own assumptions. Likewise, independently checking that each precondition is satisfiable is insufficient: the actual postcondition must imply the next precondition under one coherent retained state.

The theorem is not extrapolation to a new physical intervention. Reuse is confined to the modules' declared controls, readouts, timing and physical applicability. Holdout mission combinations must satisfy these interfaces; otherwise they are unsupported tasks, not negative evidence about a proved composition theorem.

## 9. Checking costs and the boundary of tractability

For an explicit policy graph with N_q nodes, coordinate-observation candidate filtering and local guard tests cost at most O(N_q m M), apart from physical arithmetic and enumerating observation outcomes. An action observing k uncertain binary responses has up to 2^k branches. This branching cost is real. The number of distinct reachable knowledge states can be exponential even though each state stores only O(mM) candidate identifiers. Controller synthesis, policy graph size and elapsed search are reported separately from model representation.

A more symbolic certificate can label controller nodes with factored invariants over persistent parameters, history, resource and physical abstraction variables. Let every failed obligation be expressible as a finite constraint query, such as invariant AND transition AND NOT one successor-invariant factor, or invariant AND transition AND NOT safety. If each query has an explicitly verified elimination order of induced width kappa, variable-domain bound D, and V variables, exact variable elimination decides it in O(poly(V, factor-description size) D^(kappa+1)) time and O(poly(V) D^kappa) working space. Check the rank inequalities in the same manner. This is standard CSP elimination, not a new complexity theorem.

The relevant width is the width of the full *conditioned obligation query*, including shared parameters, history, actions, resource constraints and the negated conclusion. Sparse response scopes do not imply that width is small. Scope-selection variables can have O(n^2 L^2) domains; tables or action selectors may create additional fill-in. A certificate must provide and check its width/order or report actual elimination cost. Global action selection and rank synthesis are not hidden inside these checking bounds.

In the coordinate-observation special case, product candidate filtering is exact by Theorem 1. In the strengthened aggregate class, the forest signature algorithm is exact by Theorem 1R, and joint queries use the full retained relation. Physical and mission state still couples the policy search. A full-joint reference supplied the same information can in principle achieve the same safe completion capability; the legitimate comparison is representation, discovery effort, reusable verification and actual synthesis costs, not a claim to outperform an information-equivalent optimal controller.

## 10. Scope and release conditions

The mathematical obligations above establish a concrete target for a simulation, not a measured outcome. A completed experiment must report:

- acquisition and mission records from a justified initial state, with every pulse, move, preparation, failed attempt and stop charged;
- actual versus learned/remaining scopes and threshold memories, with simulator truth isolated from learner inputs;
- whether completion is universal over retained mechanisms/support or only empirical;
- a conservative valid baseline, a fixed-decomposition baseline with the same information and honest cross-block treatment, and a small exact joint/oracle comparison where feasible;
- held-out mission compositions, not only new random replay seeds;
- local-candidate storage, evidence, interface, policy-search and certificate costs separately;
- impossible cases supported by an exact attractor or a safe-indistinguishability witness, separately from search timeouts;
- the physical calibration/support premises and the change from the predecessor's stochastic predictor to this deterministic discovery class.

The theorem does not establish that the whole original research contract is discharged, that arbitrary environmental decompositions can be learned safely, that the supplied model class is true on hardware, or that the component rank/CSP mechanisms are mathematically novel. Its intended substantive contribution is a checked chain from permitted safe records, through genuinely unknown response scopes and executable memory, to useful reusable mission completion with explicit limitations and obstructions.
