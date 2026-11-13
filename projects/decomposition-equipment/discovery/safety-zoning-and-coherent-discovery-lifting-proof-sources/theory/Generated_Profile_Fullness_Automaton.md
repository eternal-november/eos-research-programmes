# Exact generated-profile fullness criterion for record-retaining interface abstraction

Scope: an exact recognition and lifting theorem for an unbounded generated family in a restricted, explicit abstraction class. The construction uses standard finite graph-map enumeration and context-free reachability. It does not cover arbitrary component-record abstraction, claim an efficient algorithm, or by itself establish physical safety.

## 1. Data and claim
Fix FINITELY MANY interface vertices and component colors (or an explicitly selected finite sub-signature closed under the generators in use). Use the latest finite dynamic typed calculus: finite interface graphs B_v, finite component graphs W_e with legs l_e,r_e, and operations W_c -> P_B(p) commuting with outer legs. A finite original generator signature gives profile grammar N_e -> terminal e (stopping identity) and N_e -> N_e1...N_ek for every generator profile. Its language L_c consists exactly of all leaf profiles of finite generator trees of output c, including epsilon when derivable.

Let q_v:B_v -> Bbar_v be graph maps. Keep every component graph W_e and its actual state/event records unchanged; postcompose the legs with q. This gives the strict coarsening calculus morphism Q already proved in the previous milestone. Q is injective on EVERY operation fibre, including nullary fibres (which have at most one element). We seek necessary and sufficient finite conditions for:

(F) For every color c, every p in L_c, and every coarse operation wbar:W_c -> P_Bbar(p), there is a fine operation w with Qw=wbar.

Unlike bounded T8, (F) quantifies over every finite generator tree/profile and every operation on it simultaneously. Neither a common lift nor a functor section is an input assumption.

## 2. The automaton for fixed output c:a->b
For each interface vertex v let H_v=Hom_graph(W_c,B_v), a finite set. States are tagged triples (v,h,d), with h in H_v and a defect bit d in {0,1}; vertex tags are retained even when two graph-map sets happen to be identical. For readability below write (h,d) when its vertex tag is determined. The initial state is (l_c,0) at a.

For terminal color e:v->u, the labelled transition relation T_e contains

  (h,d) -> (r_e f, d OR [h != l_e f])

for every graph map f:W_c -> W_e such that

  q_v h = q_v l_e f.

Equality means equality of actual graph maps, on both states and event records. The terminal token is e; different maps f may give parallel automaton transitions, and a reconstructed counterexample must retain the chosen f.

A state (h,d) at b is BAD-accepting iff

  q_b h=q_b r_c, and (d=1 or h != r_c).

Thus the automaton matches only coarse interfaces but remembers whether any original interface matching, including either outer anchor, was violated.

## 3. Finite grammar reachability
For each nonterminal N_e with color e:v->u compute a TYPED relation R_e from automaton states tagged v to states tagged u. Initialize with T_e for the stopping production. For every generator production e -> e1...ek, add the relational composite R_e1;...;R_ek to R_e. For k=0 the original typed profile forces v=u; add only the identity relation on states tagged v, not the identity at unrelated interface vertices. Iterate to the least fixed point.

There are finitely many nonterminals and state pairs, so this terminates. A standard induction on finite derivations proves that (u,v) belongs to R_e exactly when some word p in L_e labels an automaton run u->v. Recording a derivation when a new pair is added reconstructs an actual finite profile, a generator tree, and its component graph maps f_i. Epsilon/cyclic productions do not invalidate termination or finite witness reconstruction: only retain first derivations of genuinely new relation pairs.

**Theorem B.** Property (F) holds iff for every output c the relation R_c has no pair from the initial state to a BAD-accepting state.

## 4. Proof
For a nonempty profile p=(e1,...,en), a coarse operation wbar is equivalently its component graph-map family f_i:W_c -> W_ei. Their coarse right/left boundary maps agree successively, and their first/last coarse boundary maps agree with q l_c,q r_c. This equivalence is the defining graph pullback property of P_Bbar(p), applied on actual graph maps rather than pointwise tuples.

The family gives precisely a coarse-final automaton run (its final boundary map matches q r_c); such a run is BAD-accepting exactly when the family is unliftable. It lifts to a fine operation iff every original adjacent map equality and both original outer-anchor equalities hold; precisely when the run is not BAD. Because component records were retained, any lift must have those SAME component maps f_i, so failure cannot be repaired by silently replacing the discovered witness. Thus every BAD run witnesses a genuinely unliftable coarse operation; every unliftable coarse operation yields a BAD run. Grammar reachability ranges over exactly the generated profiles, proving the nonempty case.

For epsilon, the automaton remains at (l_c,0). It is BAD iff q l_c=q r_c but l_c!=r_c. This is exactly the nullary obstruction: the unique coarse nullary operation exists but the fine one does not. Hence the same algorithm handles empty profiles without imposing q iso. QED.

## 5. Unique coherent lifting
When B passes, Q is bijective on every selected operation fibre. Let Lift denote its unique inverse. For any well-typed substitution among selected operations (whose resulting profile belongs to the generated doctrine), strictness of Q and injectivity show

  Lift(wbar substituted with ubar_i)
    = Lift(wbar) substituted with Lift(ubar_i).

The two sides have identical Q-images. Identity compatibility follows identically. Consequently every finite diagram of selected operations, including all actual presentation equations, lifts uniquely and coherently. Apply the same argument componentwise to original semantic-refinement occurrence tuples: no aggregate-only equality erases distinct components. Arbitrarily deep finite refinement trees are covered; no bound on candidate tree depth was used.

A supplied source presentation must have its declared equations satisfied by the coarse assignment. Lifting then preserves those equations; the theorem does not manufacture equations that were absent. The generated-profile doctrine is closed under the relevant substitutions by the grammar/tree substitution theorem.

## 6. Exact discovered witnesses and the nullary distinction
For nonempty p, kappa_p:P_B(p)->P_Bbar(p) is injective on both states and events because it retains tuples. If a coarse operation wbar=kappa_p w is a graph isomorphism, then kappa_p is surjective as well, and w is a graph isomorphism. Therefore B automatically lifts every newly discovered EXACT nonempty operation as exact.

For a generated empty profile, exactness needs an additional rootwise check:

  if q l_c=q r_c and q l_c:W_c->Bbar_a is iso,
  then l_c=r_c and l_c:W_c->B_a is iso.             (E0)

Fullness already gives the equality; (E0) is a finite graph-isomorphism check on the unique nullary operation. It does NOT require q itself to be iso in all cases. In contrast, PRESERVING every OLD exact nullary operation under coarsening does require q iso whenever such an operation exists. These are distinct directions and must not be conflated.

Thus B plus E0 gives coherent reflection/lifting of discovered exact operations in the generated doctrine. It does not imply preservation of every old exact operation under coarsening: a coarse profile can acquire extra tuples not covered by an old witness, making that old exact witness nonexact. Fullness alone does not prohibit unused extra tuples that no W_c-map sees.

## 7. Scope and physical reading
Finite zone-restriction colors and admissible inclusion/refinement generators can be part of the declared signature, with their actual restricted component graphs and graph maps. The theorem then covers their entire generated closure, rather than assuming all needed profile tests. It does not infer a physical sensor from a graph map: q must separately be computable from permitted information at the correct stage, and lifted controller actions must remain uniform on actual information states.

Conditional entry/exit permission certificates require their own continuation semantics (the companion theorem A). Exact witness lifting is stronger than a conservative safe-permission guarantee. An unliftable witness says that this particular discovered decomposition/route certificate is not realizable with its specified records; it does not establish that the physical task is impossible or the region unsafe.

The algorithm enumerates graph homomorphisms between finite carriers, potentially exponentially many; its value is exact structural recognition of an UNBOUNDED generated family and extraction of a finite obstruction, not a claim of tractability. It is sharper than support-only conflict graphs: a pointwise bad tuple that cannot extend to any actual graph-map family is not reported as an obstruction.

## 8. Semantic discovery is not syntactic or hardware completeness
The grammar restricts PROFILES. A newly discovered coarse semantic operation on such a profile need not be denotable by the old source generators. The theorem lifts it to a fine SEMANTIC operation; it does not express it as an old source term or physically compile a new controller. In contrast, a coarse operation already obtained by interpreting a fixed old source term has the evident fine interpretation of that same term as a lift, so existential lifting of those terms alone would be trivial. The substantial quantifier here concerns ALL new semantic operations on generated profiles and the coherence of their resulting refinement families.

A proposed extension of the source by a discovered primitive must separately satisfy physical admissibility, observation/uniformity and primitive compilation constraints, and any new equations must actually hold. Nothing in fullness makes an unavailable sensor or actuator available. A route witness also is not by itself universal safe permission: one must quantify over the initial information state, every allowed adverse execution, and nonblocking behavior as in theorem A.

## 9. Arbitrary conflict graphs occur in the exact fullness problem
This construction shows that nonexistence of a greatest adequate interface is not merely an artifact of the stronger support-graph sufficient test.

Let G be any finite simple graph with vertex set V. Use one discrete interface graph B with states V and no events. For each graph edge {u,v}, choose one orientation u,v and two loop colors c_uv,d_uv. W_c has one state z with both legs u. W_d has two states x,y with left(x)=u,left(y)=v and right(x)=right(y)=u. All component graphs are discrete. Add one generator c_uv -> [d_uv], interpreted by z->x, a valid fine operation. There are no nullary generators and no other nonidentity profiles.

The generated profiles for c_uv are [c_uv] and [d_uv]; those for d_uv are [d_uv]. For a boundary quotient q, the alternative map z->y is a coarse operation iff q(u)=q(v), but is never fine. Endomaps of W_d that change x to y or conversely likewise become newly allowed iff q(u)=q(v). These are the only extra operations in the generated doctrine. Therefore property F holds exactly when q separates each edge of G, i.e. when its fibres are independent sets.

Consequently minimal abstract boundary cardinality is the chromatic number chi(G). For three vertices a,b,c and single edge a--c, the adequate quotients {a,b}|{c} and {a}|{b,c} have no adequate common coarsening. There is no greatest adequate equivalence, although the canonical continuation quotient A exists for its different observational purpose. These statements concern semantic boundary encodings; any permitted physical observer further restricts the available quotients.

### Implementation convention for epsilon
An implementation may instead store untyped relations and give epsilon the global identity relation. For this well-typed grammar its root-query answers agree with the typed construction: every generated nonempty terminal word has the declared source/target vertices, so a run of that word is automatically anchored at those vertices; an empty child contributes only an identity step and introduces no transition or vertex change. A wholly empty root is queried only at its declared source vertex. Thus the additional unrelated-vertex epsilon pairs cannot create a spurious typed-root run. The typed relation convention above is preferable because it maintains the intended invariant at every intermediate nonterminal.
