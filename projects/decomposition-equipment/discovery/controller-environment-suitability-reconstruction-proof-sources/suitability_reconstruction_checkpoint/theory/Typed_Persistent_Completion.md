# Typed persistent completion from partial environment descriptions

## Status and intended role
This is the structural half of a controller–environment suitability theorem. Its input is a finite description presentation, not a preassembled global arena or a promise that strategy descent holds. It reconstructs a finite, possibly empty family of candidate actual worlds and witnessed decompositions. A separate causal game tests one actual controller/runner against EVERY admitted world. The finite constraint-solving and inverse-limit ingredients are standard; a novelty claim for enumeration or ordinary relational joining is not made.

The relevant open problem is not whether a hand-supplied small route is safe. It is whether several partial descriptions can jointly support one implementation, with actual environmental possibilities and persistent unknown alignment retained. The structural construction below permits crossing decompositions and nonunique record matchings. It does not infer correctness of the supplied descriptions from sensor data.

## 1. Independent finite input presentation

A chart is a finite directed multigraph G_i, with separate states and actual event records and source/target maps. Each chart carries an explicit phase type: states are decision, reply, terminal, or any fixed finite protocol phase; records carry command/reply fields at their designated phases. Identical endpoints never identify records. A completed record's label is NOT automatically a pre-action observation.

The presentation specifies:

1. A finite list of charts G_i and overlap/interface graphs J_a.
2. For every chart–overlap incidence, a nonempty finite set of admissible graph maps G_i -> J_a, all preserving the prescribed phase and static labels. A singleton is a known view map. A larger set represents unknown alignment. Choices must satisfy a finite list of explicitly supplied equalities of graph-map composites. These are independently meaningful tables and equations, not an oracle for global compatibility.
3. A set of permitted boundary maps/quotients and a finite typed quiver of prospective component colors. Prospective components are GENERATED from the reconstructed whole: their state/event carriers are quotients of its state/event sets. This rules out invisible extra component sectors. Invisible sectors require explicit bounds and a separate enumeration; they are not silently identified or discarded.
4. A finite original-calculus signature and a finite list of declared parallel equations. Generator maps are either pinned by chart anchors or unknown among specified finite typed map sets. A marked generator must be exact. All matching, anchoring and equations are checked on states AND actual event records.
5. Exact cover assertions: which charts are full images of the whole, which chart observations are literal restrictions, and which discovered decomposition witnesses must be reproduced. The basic theorem below uses full-image charts. Restricted-domain charts can be represented by explicitly supplied domain predicates and checked on those domains, but absent coverage must not be inferred to cover the whole.
6. The actual observation/action interface, initial-state predicates, objective predicates, and staged action-response interpretation. These are NOT determined merely by the graph-span calculus. They are additional operational structure that must be preserved by admissible chart maps.

A globally unknown map choice is fixed once. It is not an environment move that may be changed independently at every transition.

## 2. Explicit completion algorithm

For each admissible tuple alpha of chart–interface map choices satisfying their finite equations, construct the compatible tuple graph P_alpha. Its states are tuples x=(x_i)_i with equal interface images along every overlap; its events are tuples e=(e_i)_i with equal interface images. Source and target act coordinatewise. These are finite sets computed by equality tests on the input tables.

Enumerate state subsets S subset (P_alpha)_0 and event subsets T subset (P_alpha)_1 such that both endpoints of every event of T lie in S. Write W=(S,T). Retain W precisely when each designated full-image chart projection is surjective on both sorts, the required initial support is nonempty, and the static operational labels and phase conditions agree. For a partial chart, check its declared domain and its image separately; never demand global surjectivity of an unclaimed cover.

For each prospective generated component c, enumerate pairs of equivalence relations rho_c^0 on S and rho_c^1 on T satisfying incidence congruence:

  e rho_c^1 e' implies s(e) rho_c^0 s(e') and t(e) rho_c^0 t(e').

Their quotients form actual finite graphs Q_c. Enumerate the allowed boundary maps and unknown typed generator maps among actual graph maps on these finite carriers. Required whole-to-component maps are the quotient maps; a requested map Q_c -> Q_d induced from the whole is available exactly when ker(p_c) is contained in ker(p_d) on both sorts, and is then uniquely determined. Any extra allowed component map must belong to the independently specified finite interface language, not merely exist as an arbitrary set map.

For every generator g:c -> (c_1,...,c_k), construct the compatible tuple graph using the stated boundary maps and check its actual graph map. Marked exactness is bijectivity on states and events, including the k=0 boundary graph. Check anchors to the supplied chart witnesses by evaluating the corresponding maps. Interpret every declared finite equation using occurrence-indexed substitution in the original dynamic calculus and compare the two actual maps. The existing dynamic calculus theorem supplies all algebraic laws; finite equation satisfaction is not replaced by same-state behavior or trace equivalence.

Classify every input choice by its meaning. A PHYSICAL uncertainty changes the possible system/observations, for example an unknown persistent sensor-to-world binding. A MATHEMATICAL witness is a proposed decomposition, quotient coordinate, or proof matching; it does not by itself change the environment. An IMPLEMENTATION choice belongs to the controller architecture. These roles are not interchangeable.

Retain each complete realization as a pair (omega,d), with omega its physical completion and d its mathematical decomposition witness. The finite set of such pairs is Xi. Separately retain the physical completion set Omega computed from the physical chart facts BEFORE filtering by optional candidate decomposition requirements, and define D(omega) as the fibre of admissible mathematical witnesses. A physically possible omega with D(omega) empty is a failure to find the demanded decomposition certificate, not a nonexistent physical world. Only an explicitly supplied physical assumption that such a decomposition exists may filter that world at input time.

Do not replace a physical omega by only its unlabelled graph W: different physical record alignments can change observation/implementation anchors. But do not universally quantify over pure coordinate/proof choices as if they were adverse physical states either. All sets and fibres are effectively constructed from the finite input; no global common refinement is assumed.

This is an exhaustive correctness algorithm, not an efficiency claim. The number of supports, equivalence relations, and graph maps can be enormous. A useful implementation should exploit the presentation's factorization and separators rather than materialize every completion. A bounded-width or symbolic refinement of the algorithm needs its own theorem.

## 3. Soundness and completeness of generated reconstruction

**Theorem 1.** Xi is in bijection, up to component-carrier renaming, with all generated witnessed realizations of the supplied presentation whose chart projections jointly separate whole states and whole event records and whose whole contains no state/event invisible to the chart tuple. Every member has exactly the specified chart images, typed generator maps, markings, anchors, and equation interpretations. Xi is empty exactly when no witnessed realization in this declared class exists. This does not imply that the physical completion set Omega is empty.

**Proof.** Soundness follows from the explicit subgraph, incidence, map, image, marking and equation tests. For completeness, let R be a realization. Its chart maps yield a map R -> P_alpha; the overlap equations ensure that this lands in P_alpha. Joint separation makes the map injective on both sorts. Identify R with its image subgraph (S,T). Every generated component is the quotient by the kernel of its surjective whole projection, and its event kernel respects incidence. Hence the enumeration includes isomorphic copies of all its components and maps. All constraints are invariant under these identifications, so the corresponding complete tuple is retained. Conversely two representatives with the same actual image/choices differ only by the declared component-carrier renaming. If named actual component records are part of the anchors, their names must instead be retained, and this last renaming quotient is not taken. QED.

The joint-separation/generatedness restriction is substantive. Multiple global events can share the same tuple of chart events; unbounded invisible multiplicity cannot be reconstructed by this construction. Such models need explicit additional record carriers and bounds or a different completion theory. The theorem therefore does not pretend that arbitrary partial descriptions identify every real environment.

Crossing is not excluded: the component quotient kernels need not form a chain or a laminar family. Exactness and anchor tests decide whether the proposed crossings admit a jointly realizable refinement in this class. The algorithm rejects incompatible crossings rather than assuming a shared refinement. Mere nonemptiness of each local projection is insufficient.

## 4. Persistent operational interpretation

For each PHYSICAL omega, its phase-compatible operational data induce the actual arena A_omega. A selected d in D(omega) supplies decomposition projections of that arena, not extra environment moves. Its state is a whole state together with the chosen controller's memory state, not merely a vector of chart observations. Every transition records its actual component-event tuple and its static matching omega. Distinct adverse records stay distinct.

The unknown environment arena is the disjoint union over omega, with omega retained as an immutable hidden coordinate. Initial uncertainty contains all specified initial states of every omega. The runner observes only the separately declared physical observation/history interface. In particular, having constructed a tuple of all chart states does not grant the controller access to it.

**Theorem 2 (all-history reconstruction).** For every finite length n, executions in the disjoint-union arena are exactly pairs (omega, h) where h is a length-n execution of the reconstructed world A_omega. Their chartwise projections are actual compatible local histories with one unchanged matching omega. These correspondences commute with truncation, concatenation with the SAME omega, and original-calculus exact occurrence refinement. The same statement holds for infinite executions.

**Proof.** At n=0 use the disjoint-union state definition. At each step the transition relation preserves omega and supplies the actual aligned tuple; induction gives finite paths and the inverse reconstruction. Truncation and same-omega concatenation are coordinate restriction/concatenation. Exact occurrence refinements give state/event bijections, and the original dynamic path theorem transposes time and occurrence coordinates, including repeated occurrences and nullary branches. Therefore refinement commutes with path reconstruction whenever it also preserves the additional phase/action/observation structure. Infinite paths are sequences of the same finite coordinate data. Alternatively, if every prefix has some consistent completion, the admissible-completion sets form a descending nonempty sequence of subsets of the finite set Omega; their intersection is nonempty, giving a single completion for the entire path. This alternative requires prefix consistency, not independent edge consistency. QED.

A stream whose every transition can be explained by SOME completion need not admit ONE completion explaining all transitions. Replacing persistent omega by an independently reselected per-step completion is a different environment semantics. It can erase learnable information and invent adversarial executions; choosing omega separately to justify each controller decision can also invent a nonexistent implementation.

## 5. Controller and environment choices have different quantifiers

The set Omega describes uncertainty about the PHYSICAL environment, universally quantified. Pure decomposition witnesses d belong to D(omega), not to the adversary. A prospective controller realization kappa is an implementation choice, existentially selected ONCE. If its own local descriptions have unresolved crossing matchings, enumerate them separately using the same finite typed construction, obtaining Kappa. Do not mix the two roles into a single existential joint-completion test.

For a fixed controller, Kappa is a singleton containing its actual representation, or a set of representation choices proved operationally equivalent. For a bounded controller architecture, Kappa contains implementations satisfying the specified hardware/observation constraints and memory bound. An unrestricted distributed synthesis algorithm is not claimed.

Suitability has the order

  exists kappa in Kappa, exists one permitted causal runner pi,
  for every physical omega in Omega, exists a coherent d_omega in D(omega),
  for every admissible initial state and adverse execution of that SAME
  (kappa,pi,omega), the task holds and d_omega witnesses the declared realization.

The mathematical witness may vary with omega without being observable to the runner, because it is proof data, not a runtime action. Every physical table/store/communication operation remains selected before omega. If the application instead demands ONE fixed decomposition witness independent of the actual world, move d outside the universal quantifier and state this strictly stronger target. If a proposed witness choice is itself used as a runtime selector or adapter, it is an implementation choice and must obey that earlier existential quantifier and actual information access. These distinctions prevent both an overly adversarial interpretation of arbitrary factorizations and a hidden-state-dependent controller.

Require Omega nonempty. A controller–world interface mismatch is a failure for that world, NOT a reason to remove the world from Omega. Otherwise an inappropriate controller could pass by excluding every inconvenient environment. Likewise an empty admissible-action set is blocking failure, not vacuous universal safety success.

The accompanying witness-information game supplies a finite, non-tautological decision criterion for safety and guaranteed termination in this finite class. Its hidden states retain (omega,actual state,controller memory) jointly, and its action choices are permitted causal hardware programs, not arbitrary functions of hidden coordinates. The structural algorithm above supplies its arena from the independent presentation; the game theorem does not assume that strategy descent already holds.

## 6. What this does and does not advance

The construction addresses finite simultaneous realization and the distinction between environment semantics and induced modal verdicts. It connects original occurrence-indexed decomposition syntax to actual persistent uncertainty and all-history controller interaction. It does not claim new general CSP theory, novel generic causal-strategy gluing, a universal virtual-equipment presentation, an unbounded distributed-synthesis procedure, or empirical model identification. It does not prove that every graph-isomorphism preserves controller suitability: phase, choice ownership and observation timing are essential extra structure.

For the original contract this is a bounded contribution toward I1/I2/I4/I5 and semantic use G, not discharge of E2 or the full 2-Segal/recognition program. In particular, exhaustive finite completion alone is not a satisfactory practical achievement. The significance test is whether the persistent/causal reconstruction theorem exposes real incompatibilities that per-chart controller tests and ordinary structural gluing cannot detect, and supports usable factorized algorithms or a substantive family with proven separations.
