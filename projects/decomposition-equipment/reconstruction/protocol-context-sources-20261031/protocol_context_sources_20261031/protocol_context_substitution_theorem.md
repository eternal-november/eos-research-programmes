# Token protocol contexts, substitution, and reconstruction at every tree cut

31 October 2026. Derived scoped theorem; no novelty claim. This constructs an actual operational composition language and its coherent cylinder comparisons. It is not a theorem for all concurrent, instantaneous-feedback, or physically realizable systems.

## 0. What is new relative to the fixed-context checkpoint

The previous checkpoint reconstructed workers in one given asynchronous context. Here we define operations that can themselves be inserted into operation holes; derive their positive kernels and substitution laws; prove interface sufficiency for any subtree from a primitive information-flow discipline; and construct compatible finite-path realization arrows for every refinement of a decomposition-tree cut. Thus reconstruct-at-leaves then wire and reconstruct-the-whole-network are connected by actual commuting realization maps. The canonical comparison cells are consequences of those maps, not assumptions about an unspecified assembly functor.

The construction is restrictive in a visible way: a root tick makes at most one ultimate worker call through a finite stack of context calls. All internal routing and return computations are atomic, normalized, and cost zero additional root ticks by convention. Context nesting does NOT replace a hierarchical scheduler by a flat one. Arbitrarily many hidden worker calls within one tick, infinite call stacks, instantaneous recursive equations, and hidden coupling across component boundaries are not included.

## 1. Colors and operational operations

Fix a set-sized palette of protocol colors and chosen representatives of countable state/record sets; all matrices subsequently used lie in a chosen small category containing their actual maps. For the operad definition, first fix each primitive context's preparation; the preparation-indexed family version is pointwise, with substitution taking tuples of preparation labels and associativity/unit maps rebracketing these tuples together with state and record tuples.

A color A is a pair of nonempty countable sets (U_A,O_A), with declared meanings for input/output marks (resource requests/replies, interventions, tick observations, termination, refusal, etc.). Types guarantee alphabet compatibility, not termination or fairness. If an application has protocol legality predicates, illegal transactions are represented by declared error/refusal behavior; alternatively one can restrict to invariant-preserving implementations after proving closure of that invariant. No such restriction is used to hide deadlock here.

An n-ary context C:(A_1,...,A_n)->B has:

* countable persistent state S_C and a normalized initial law mu_C^a for each declared preparation a;
* countable pending-record set Z_C;
* a normalized pre-query kernel A_C(s,u;d,z), where d is either `local` or a pair (i,v) with v in U_Ai;
* normalized post-reply kernels B_C(z,r;s',o), with o in O_B and r in O_Ai when the pending query is (i,v), or r=star for `local`.

The pending-record type remembers the branch and any information needed by the post kernel. Formally one can take Z_C to be branch-indexed, or include d in its argument. As a mandatory normal form, EVERY primitive pending record retains the incoming persistent state, incoming boundary input, and chosen branch/query, in addition to its sampled auxiliary record. This is without loss of transition semantics: replace any record z by (s,u,d,z), and let the post kernel ignore the added fields. The pre kernel is supported only on records whose stored incoming fields match its actual arguments and selected branch; record isomorphisms are understood over those incoming fields. These fields are mandatory even when the original post kernel did not need them. Consequently compilation and identity insertion add only constrained duplicates/singleton fields, rather than extra unconstrained information that could invalidate a record-level unit isomorphism. Outputs or events wanted for observations can be included in o or in an explicitly retained internal log. These kernels are genuinely stochastic; no transition may conceal a nonterminating computation.

One call of C first samples (d,z). In the local case it invokes no hole and runs B_C(z,star). Otherwise it calls hole i once on v, receives r, and runs B_C(z,r). Unselected holes retain their state. The complete call costs one tick at C's external boundary. A selected child call is a subroutine within that same root tick, not an additional root tick. This timing convention is part of the operation.

A worker of color A is the nullary case, equivalently a countable stochastic Mealy machine K(s,u;s',o). Its pre/post presentation can be deterministic pre plus K post. A context manager can implement mutex ownership, busy responses, round-robin position, deadlines, refusal, recovery, random interventions, and arbitrary history-dependent decisions in its state. A fixed finite population of slots is sufficient. Scheduler and manager are not implicit infrastructure.

Shared resources must have ONE owner/manager whose information reaches descendants through typed messages. Inserting two copies of a manager changes the system. A context needing a descendant's pending action must store its previously reported action or obtain it via an explicit protocol; it may not inspect a hidden worker state.

## 2. Substitution is an explicit stochastic construction

Let D_i:(A_i1,...,A_ik_i)->A_i. The substituted context C[D_1,...,D_n] has persistent state

    S_C x product_i S_Di,

and holes indexed lexicographically by (i,j). Its initial law is the actual product of the declared node initial laws, conditional on any declared common preparation parameter. Section 5 states the scope of this independence discipline; an arbitrary hidden correlated initialization is not replaced by a product.

Given (s_C,s_1,...,s_n),u, its pre kernel performs:

1. sample (d_C,z_C) using A_C;
2. if d_C=local, select no ultimate hole and store z_C plus the inactive child states;
3. if d_C=(i,v), sample (d_i,z_i) using A_Di(s_i,v); if d_i=(j,w), select ultimate hole (i,j) on w; if d_i=local, select none;
4. retain a pending record containing the original tuple, selected branch, z_C and (when present) z_i. Pending records are well-formed node-addressed records: duplicate state fields introduced by repeated compilation are constrained copies and are canonically removed, not freely varying extra coordinates.

The post kernel first runs B_Di on the ultimate reply (or star) if a child was entered, obtaining s_i',r; then runs B_C(z_C,r), obtaining s_C',o. It changes exactly the visited persistent states. If C selected local, it runs only B_C. All unvisited states are unchanged.

These are countable stochastic kernels: each branch is a finite product of normalized nonnegative kernels; summing outputs in reverse evaluation order gives one. Summing over the countable intermediate records yields a normalized kernel. This calculation does not assume a global normalization or progress theorem.

The identity on A has singleton state, deterministically queries its sole A-hole with the received input, and returns that reply unchanged. It does not introduce an observable primitive tick or an observable routing event. Permuting holes merely reindexes tags. Nullary contexts and local branches are allowed.

### Substitution theorem

Modulo canonical bijections of product states and pending-record tuples, these operations form a colored symmetric operad. Equivalently, before choosing representatives they form an operadic structure coherent up to the specified state/record isomorphisms.

Proof: expand any finite nesting into its root-to-leaf call stack and reverse return stack. Each root call visits a finite path, possibly ending at a local branch, and hence at most one ultimate hole. For each fully specified stack record, its probability is the product of the same pre factors in downward order and post factors in upward order, whatever order substitution was compiled. Intermediate summations are over the same countable records; Tonelli permits their reassociation. The persistent state update is the same assignment to the same visited nodes. Thus both bracketings have the same kernels under the explicit state/record bijections, not merely the same final output distribution. Identity insertion adds only singleton coordinates and deterministic forwarding. Removing these is a kernel isomorphism. Permutations respect node/leaf labels. All associativity, unit, and equivariance diagrams commute because each route sends a tuple/record to the same node-addressed tuple/record. QED.

The semantic interpretation in stochastic stateful transducers is therefore genuinely substitution-preserving. The numerical flattened post kernel marginalizes intermediate child replies; those replies cannot generally be recovered from that kernel alone. Whenever node-level path records are used below, they belong to the canonical EXPANDED execution of the given realized context tree, obtained by retaining the intermediate samples in this composition formula. We do not claim an internal-log bijection for arbitrary black-box implementations that merely share the flattened numerical kernel. The proof is not the assertion that freely generated syntax has an operad.

### Scheduler qualification

If an outer scheduler alternates between a two-worker subgroup and a one-worker subgroup, and the inner two-worker scheduler alternates its leaves, the global leaf schedule is A,C,B,C,... . Flat three-worker round robin is A,B,C,A,... . These are distinct semantic operations. The theorem equates different compilations of the SAME nested scheduler; it does not equate those two schedulers. To represent flat RR via a hierarchy, the root must retain the global cursor and forward an explicit leaf-routing token through transparent descendants. That is a separately specified implementation, whose kernel can be checked to match flat RR.

## 3. Positive subtree cylinders and history machines

Fix a finite typed tree T of contexts with worker leaves. A subtree v, viewed at its outer color, is itself a positive normalized stateful transducer by Section 2; its state is the product of its descendant node states. It has no access to its enclosing context except its boundary input stream.

For each declared subtree preparation a_v and each deterministic imposed input word u_1...u_n, sum its actual hidden state paths to obtain

    p_v(o_1,...,o_n || u_1,...,u_n; a_v).

Finite products and countable sums make these actual nonnegative probabilities. Normalization and causal prefix consistency follow directly by summing the last transition. Define

    K_v(o | h,u) = p_v(h,(u,o))/p_v(h)

when the denominator is positive, with a normalized arbitrary continuation when it is zero. The preparation label a_v is part of h. This defines a countable positive history-state realization R_v. The construction uses only the outer controlled cylinder of subtree v, not the whole enclosing network.

An outer history machine retains the history of calls to that subtree. It does not append a local call on root ticks when that subtree was not selected. Root timing and routing remain controlled by the explicit surrounding context.

## 4. Primitive discipline and conditional sufficiency, proved

For each preparation, initial private node states are independent; fresh transitions use independent innovations conditional on their stated local state/input, independently of all other primitive innovations. A public/common preparation parameter may index these laws, provided it is explicitly included in the cylinder preparation labels and the claim is conditional on it. More generally shared randomness may live in an explicit source/manager node and influence components only through their boundary messages. It is NOT valid to take unrelated marginal cylinders and assume their hidden coupling is a product.

Consider any subtree B and its surrounding context E, which includes other branches and all ancestor managers/schedulers. The disjoint private innovations of B and E are independent initially. A complete finite boundary transcript records every call input/output between B and E. Retain E's actual current private operational state and its past state/interaction record, stopping IMMEDIATELY BEFORE the next B response. Include current ancestor pre-call pending records and the selected input. Do NOT include post-return ancestor states after the response being predicted: those may reveal that response. Do not retain unrevealed private state or future tapes of B in this conditioning.

For any fully specified internal finite B path x compatible with a fixed past boundary transcript h, and any fully specified exterior finite record e stopped at that pre-response boundary, the joint path weight factors as

    w_B(x; h) * w_E(e; h).

Only past exterior factors and the current pre-call factors appear, never future post-response factors. The exterior factor depends on B only through its reported boundary transcript: it has no channel to x. The interior factor depends on E only through the boundary inputs in h. This factorization follows by grouping primitive pre/post transition factors by which side of the boundary owns them; interruptions and unselected ticks contribute only exterior factors. It does NOT assert unconditional independence of the resulting traces.

Sum over the internal x compatible with h. For any exterior record of positive probability, its common exterior factor cancels in the conditional distribution of B's next response. The result is precisely K_B(-|h,u). If an exterior record hides some of its own random choices, sum the nonnegative exterior factors first; the same cancellation applies. Thus

    Law(next B output | h, retained exterior past/current private state,
                         selected B, supplied u)
      = K_B(-|h,u).

This proves the strong private-context-state closure needed for reconstruction. The exterior selection/update kernel is also its specified kernel on its actual state: that follows directly from its private-innovation implementation. The argument applies to EVERY subtree and to networks in which any other disjoint subtrees have already been replaced by history machines, since those machines also have private innovations and boundary-only interaction.

Zero controlled-prefix histories remain unreachable. If a positive global record first entered a locally zero extension, the displayed conditional kernel would give that extension probability zero, a contradiction.

This is a concrete sufficient discipline, not a necessity theorem. A physically correlated system may instead prove the required conditional laws directly. Merely postulating those laws for every substituted context would shift the problem into an assumption; here their stability is derived for the stated implementation language.

## 5. Reconstruction at every cut, and the actual path maps

A cut F is a finite frontier of nodes: no two are ancestor-related, and every root-to-worker-leaf path meets exactly one selected node. Let T_F retain every original context strictly above F and replace each entire subtree rooted at v in F by R_v. The finest cut is the worker leaves; the coarsest is the root alone. A root worker presents the trivial case.

Every T_F has the same outer controlled cylinder as T. Proof: replacing one disjoint subtree preserves the joint law of the retained exterior state/interaction record by Section 4 and finite-prefix induction. Replace the finitely many selected subtrees successively. This proof derives compatibility from the primitive discipline and uses the actual joint law; it does not synthesize a network from marginal output distributions.

For rigor across preparations, fix a countable family a of node preparations, with its subtree restriction a_v; experiments are e=(a,n,w), root horizon n and imposed root-input word w. The same a labels all compared realizations, including the root history. Public/common parameters are retained in these labels. An undisclosed random mixture of preparation parameters cannot be forgotten unless its conditional-sufficiency claim is separately proved.

Let X_T be the countable disjoint union of all tagged finite original paths through horizon n, including node states and completed pre/query/post records. In particular, record the invocation input/output of EVERY visited internal node, including a call that ends in that node's local/no-child branch; without those records a later coarser cut need not be calculable. Let X_F be the analogous path carrier for T_F, including states above F, history states at F, and all their retained interactions. Include all well-typed syntactic paths, including zero-probability ones, so the maps below are total. Identity forwarding has no separate event; its singleton state coordinates may be canonically removed.

There is a deterministic q_F:X_T->X_F: retain above-cut states and events, erase internal states and records below F, and calculate at each cut node its boundary input/output history from the erased subtree's calls. Countable normalized path preparations satisfy

    (q_F)_* p_T^e = p_F^e.                                  (1)

This is stronger than root-output equality: it retains all context private state above the cut. Its proof is Section 4's conditional law followed by induction on root ticks, with finite expansion of each tick's stack. Coarse-to-fine hidden records need not be recoverable.

If F refines G (every F-node lies at or below a G-node), define

    q_FG:X_F -> X_G

by retaining states above G, forgetting the additional below-G implementation/history states, and accumulating each G-node's boundary history. Even though the G-history kernel was defined from the ORIGINAL subtree rather than T_F, the substituted subtree has the same controlled cylinder by the preceding theorem. Therefore the same proof gives

    (q_FG)_* p_F^e=p_G^e,
    q_FG q_F = q_G,
    q_GH q_FG = q_FH,    q_FF=id.                            (2)

The last two identities are deterministic record identities: forgetting in stages forgets the same coordinates; accumulating the boundary history twice with inherited prefixes produces the same history, not a fresh restart. They hold for syntactic zero-probability paths too when carriers use consistent accumulated-history records.

For incomparable cuts, a common refinement exists (take the lower node on each branch). Both routes to any common coarsening commute by (2). Rebracketing nested contexts commutes with all these maps under the node-addressed record bijections of Section 2. Prefix restriction also commutes as a deterministic record map. It changes the experiment/test indexing and requires the corresponding reindexing bridge; it is not asserted to be an arrow of one unchanged Fact(r). This gives a genuinely coherent FAMILY of reconstruction comparisons under nested context substitution, rather than separate equalities for independently chosen fixed contexts.

The strongest operational diagram includes

    original hidden network paths
        | q_finest                 | q_root
        v                          v
    leaf-history network paths --> whole-network history paths.

The horizontal arrow forgets internal contexts/routing and records the outer history. It is not asserted invertible; information relevant only to internal tests is deliberately absent at the root. If those tests are required, keep them in the boundary protocol or stop at a finer cut.

## 6. Honest joint cylinders and canonical comparison coherence

Use the SAME outer preparation family e and SAME outer finite-prefix indicator tests t (plus total-mass test) for every cut. Let b_F^t be the corresponding indicator on X_F. Since every q preserves the outer marked trace,

    b_G^t q_FG=b_F^t.

Together with (1)-(2), the actual path distributions give ONE joint cylinder

    r_(t,e)=b_F^t p_F^e=b_T^t p_T^e.

In a small countable nonnegative matrix category containing these carriers and maps, q_F and q_FG are honest arrows in Fact(r). All preparations were derived by multiplying the actual primitive transition laws and summing genuine hidden records. There is no fabricated independent product of observed marginal laws.

Embed by J into the free Isbell envelope and apply the already proved source-changing normalizer construction. Write

    C_F=(JX_F <-M0 G_F ->E0 R_r).

Each Jq_FG induces its uniquely determined map G(q_FG):G_F->G_G preserving the preparation cocones, left legs and right legs into R_r. Existing orthogonality gives

    G(q_GH) G(q_FG)=G(q_FH),   G(id)=id.

Thus the operational cut/refinement diagrams and context-rebracketing diagrams induce coherent canonical comparison-of-spans cells, with changing source boundary Jq and fixed target R_r. No q is assumed M0/E0 or invertible. The formal apex is not assumed a stochastic implementation.

This is the justified categorical formulation: an actual colored operad of token contexts; for each realized tree, a covariant diagram of actual finite-path realizations indexed by cut coarsening; and the coherent source-changing normalizer diagram of that SAME joint cylinder. It is not yet an operad action on all arbitrary Isbell objects, nor a claim that every canonical comparison can be physically wired.

Changing the tree by genuine substitution changes its cylinder in general. The law says that a fixed substituted tree can be compiled, decomposed, and reconstructed at compatible levels coherently. It does NOT identify cylinders of arbitrary different networks. Nested substitution coherence is the node-addressed compilation/cut coherence proved above, not an unsupported equality across unrelated cylinders.

## 7. Progress remains separate

Busy/deadlocked/starving contexts are normalized operations and are never excluded by typing. A busy state may later be rescued by an intervention; it is not made absorbing unless the actual context declares halt. Real termination may be padded by a declared terminal symbol. Infinite behaviors are obtained from finite cylinders in countable sequence spaces, not as a countable carrier of all infinite paths.

Exact trace equality transports trace-defined progress properties. Establishing them requires a separate rule, for example the completed ordered-lock/cyclic-scheduler two-matrix theorem, whose hypotheses remain visible. Applying that theorem requires that the ACTUAL flattened scheduler satisfy its W-tick service condition. Hierarchical RR does not inherit the same constant merely by operadic associativity. A compositional calculus of quantitative certificates would require its own substitution theorem and is NOT claimed here.

## 8. Exact boundaries and next obstruction

1. Countable states, finite tree depth and at most one leaf call per root tick are substantive restrictions. Multi-call ticks require an explicit finite/possibly divergent local execution semantics and a separate timing/admission theorem.
2. Only causal delayed interaction is represented. Feedback through stored state and later ticks is present; arbitrary zero-delay feedback, compact trace, or general gluing is not derived.
3. Hidden correlated worker/context preparations can break closure despite identical local controlled cylinders. The earlier private-bit counterexample still applies. An explicit coupling/source/interface extension is required.
4. Resource ownership is global only when its explicit manager is global. Tensoring two hidden copies is not shared-resource wiring.
5. Complete exact cylinders need not be statistically learnable, compact, computable, or physically implementable. History realization is a positive mathematical machine, not an efficiency result.
6. The formal comparison is coherent for the actual outer cylinder. Arbitrary internal tests cannot survive a root-only abstraction without being exposed at its boundary.
7. The general two-sided program remains broader: doctrine-independent intervention/gluing constructions, controlled comparisons for noncausal/partial feedback, and physical descent are not proved by this scoped operational result.
