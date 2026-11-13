# A separate substitution law for polling envelopes and ordered-lock progress

31 October 2026. Companion to `protocol_context_substitution_theorem.md`. Classical scheduling/resource-order ingredients, derived in the explicit token-context semantics. No novelty claim. This supplies a concrete certificate composition rule; it is not a blanket lax-functor claim for every possible progress bound.

## 1. Uniform polling certificates

An operation C with n holes has a polling certificate L=(L_1,...,L_n), positive integers, if on EVERY legal finite execution record of C, each block of L_i consecutive activations of C contains at least one call to hole i. The statement is uniform over the incoming input sequence and legal hole replies and covers every possible internal scheduling choice. Here a legal finite record uses positive-support context pre/post transitions from an admitted preparation, while its external inputs and hole replies range over arbitrary values permitted by the declared interface protocol. Thus the certificate is robust against every such reply, not merely replies likely for one chosen worker. These supported context records are distinct from the larger zero-probability syntactic path carriers used to make reconstruction maps total. It refers to hole calls, not successful resource grants. A context with random scheduling qualifies only when all its possible finite records satisfy this bounded-gap property; almost-sure eventual fairness is insufficient.

Activations mean the operation's own boundary calls. Finite traces shorter than L_i impose no window condition. Quantification over all legal traces includes any continued trace on which the context remains activated. Terminal workers remain normalized absorbing no-op machines, and the context continues polling them in its mathematical execution. Mission completion is the stopping event that all workers have reported terminal, not permission to erase later polling from the certificate semantics. Actual execution may stop at that event because all bounds below concern only preceding windows.

A blocked attempt ALWAYS calls its worker with a busy input. The busy worker kernel deterministically stutters its intrinsic operational state, holdings, and pending action, though a history realization records the busy interaction. A granted input advances exactly one intrinsic step. A terminal worker replies by its absorbing no-op. This encoding is needed: an implementation that handles busy entirely as a context-local no-call cannot automatically reuse a CALL certificate.

The forwarding identity has certificate (1). A deterministic cyclic context on k>=1 holes has certificate L_i=k, independently of all legal replies and incoming values, provided it continues polling terminal holes. This is an implemented scheduler fact, not a fairness premise. Nullary operations have an empty certificate. Contexts with starvation or unbounded no-call runs remain perfectly legitimate semantic operations; they need not admit a certificate.

## 2. Substitution theorem

Suppose C has certificate L_i and each D_i has certificate M_ij. Then C[D_i] has certificate

    N_(i,j)=L_i M_ij.

Proof: take any block of L_i M_ij consecutive activations of C[D_i]. Partition it into M_ij consecutive blocks of L_i activations. Each contains a call to D_i by the outer certificate. Thus D_i is called at least M_ij times during the whole block. Its calls occurring in this interval form a consecutive segment of its own activation stream, since every such activation is a call from C. Choose M_ij consecutive ones. The inner certificate forces a call to j among them. Substitution executes exactly that call within the corresponding root activation, so the outer window contains a call to (i,j). This argument applies to every actual legal record and requires no probabilistic independence. QED.

Certificates admit upward weakening: if L is valid and L' >= L componentwise, then L' is valid, because every L'_i-window contains an L_i-subwindow. Product substitution is monotone in both outer and inner positive integer bounds. Thus certified pairs (C,L), ordered from stronger/smaller to weaker/larger bounds for a fixed C, form a monotone substitution calculus; this claim follows from the proved window rule and ordinary arithmetic, not from an unspecified lax structure on arbitrary progress proofs.

The certificate obtained by iterated substitution at a leaf is the product of its local bounds along its root-to-leaf path. Multiplication is associative, identity contributes 1, and hole permutations merely relabel bounds. Hence this particular certificate assignment is coherent under the same substitution/rebracketing maps as the operational context theorem. The rule is sound rather than necessarily optimal: a directly analyzed flattened scheduler may admit smaller constants.

A fully certified tree with W worker leaves therefore has finite bounds L_a for each leaf a and

    B=max_a L_a.

Every B-root-tick window contains a call to each worker. A hierarchy alternating a two-worker group with a singleton group has bounds 4,4,2, so B=4; flat three-worker round robin has B=3. The theorem does not identify their traces or rates.

## 3. Required shared-manager embedding

To use these polling certificates for mutex progress, fix ONE authoritative root resource manager, not one independent manager copy per subtree. Its persistent state stores actual resource ownership and each worker's last reported pending action and terminal status. A selected worker's attempt must be resolved from this authoritative state.

A concrete permitted implementation passes a read-only root resource snapshot and routing data down the selected hierarchy. Once the ultimate leaf is chosen, its grant/busy input is calculated from the snapshot and its reported pending action. A busy response stutters. A successful response reports its exact atomic resource operation, release/completion/reentry marks, and next pending action. These are returned along the call stack and committed by the sole root manager in its post phase. Every root tick makes at most one leaf call, so the snapshot cannot become stale through an intervening competing leaf operation within that tick. The child controllers may update only their own scheduling/routing state; they do not independently mutate or duplicate resource ownership.

This is an explicit implementation discipline for this theorem, not a theorem saying arbitrary manager placement respects composition. Any other design needs its own equivalence or invariant proof. If manager metadata or pending actions are observed by a worker and affect its intrinsic law beyond grant/busy, the autonomous-kernel hypothesis below must be replaced by a proved uniform controlled contract.

## 4. Deterministic service lemma

Assume W>=1 fixed worker slots, finitely many mutexes with a strict total order, no ownerless locks, and the previously proved ordered-lock protocol:

* each new acquisition is strictly above every resource currently held;
* finishing releases all held resources;
* the only blocking reason is a requested mutex held by another worker;
* busy attempts and terminal no-ops change no intrinsic worker or resource state;
* a nonblocked unfinished worker, when called, performs one successful intrinsic transition;
* only the successful leaf operation changes resource ownership or a worker's pending action.

Then every unfinished configuration has at least one runnable worker. Otherwise every unfinished worker waits for a mutex owned by another unfinished worker. Following owner edges in a finite population yields a directed cycle. Each holder's next requested mutex is strictly larger than the mutex it holds for its predecessor, forcing a strict increase around the cycle, a contradiction. Internal-step/release workers and workers requesting a free mutex are runnable.

In any B-tick window throughout which the mission is unfinished, at least one successful intrinsic transition occurs. Suppose none occurs. All worker intrinsic states, ownership and pending actions therefore remain fixed, though scheduling cursors may change. A runnable worker at the start remains runnable. Its polling envelope supplies a call within the window, and the authoritative manager grants its runnable operation, contradiction.

Let S count the FULL latent intrinsic work of all episodes actually entered, including the as-yet-unrevealed remaining intrinsic work of entered but uncompleted episodes; it is not merely the number of successful transitions already observed. Thus if S<infinity, global completion occurs within B*S ticks. Equivalently, on an event where at most K successful intrinsic transitions are required and no additional episodes occur, T<=BK. If the system were still unfinished after BK ticks, the B-window lemma would have supplied at least K successes; exhausting K required successes while unfinished would require an additional transition and contradict the event's definition. This is the same equality-case argument as the earlier cyclic proof.

No claim is made that EVERY blocked worker succeeds within B ticks. B bounds calls; successful service is guaranteed globally. Starvation freedom follows later from finite total work, not from granting every lock promptly.

## 5. Quantitative two-matrix consequence

Retain the previous concurrent theorem's exact local assumptions. Episodes have finitely many modes i, countable entries x, finite potentials v_i(x)>=1, intrinsic duration L (successful transitions, disregarding availability delays), and conditional bounds at actual entry

    Pr(L>t | revealed past, entry i,x) <= b_i(t)v_i(x), b_i(t)->0;
    Pr(next mode=j | revealed past, entry i,x) <= p_ij;
    E[1_next=j v_j(Y) | revealed past, entry i,x] <= g_ij v_i(x).

The conditioning excludes unrevealed future private tapes. The actual successful-grant path is a prefix of the autonomous intrinsic path: the context may delay but not alter its transition law. Releases/reentries are reported and committed under Section 3. Let P=(p_ij), G=(g_ij), rho(P)<1, and worker a start at (i_a,x_a), v_a=v_i_a(x_a). No rho(G)<1 is needed for the following statement.

For integers m,t>=1,

    Pr(T > B W m t)
      <= sum_a (P^m 1)_(i_a)
       + sum_a v_a [sum_(k=0)^(m-1) G^k b(t)]_(i_a).       (E)

Proof: the earlier nonnegative prefix-domination argument applies unchanged. Actual next-entry indicators/rewards are bounded by their latent intrinsic counterparts: starvation suppresses successors rather than creating them, and completed successors agree. Consequently the probability a worker enters more than m episodes is bounded by (P^m1)_i_a. Conditional entry-potential induction and a union bound give the second term as an upper bound on any of the first m actual episodes per worker having intrinsic duration greater than t. Neither argument conditions on eventual completion. Outside these bad events, at most Wm episodes occur and each requires at most t successful transitions; hence S<=Wmt. Section 4 gives T<=BWmt. QED.

For fixed m the second term tends to zero as t tends to infinity. Then rho(P)<1 lets m tend to infinity, proving almost-sure global completion, eventual release and absence of permanent starvation. Infinite expectation remains possible.

If additionally E[L|entry i,x]<=c_i v_i(x) and rho(G)<1, nonnegative summation of expected episode work gives

    E[T] <= B sum_a v_a [(I-G)^(-1)c]_(i_a).

Taking B=W for a flat cyclic W-worker scheduler recovers the earlier W^2mt tail cutoff and W multiplier on expected work. A hierarchical scheduler uses its own derived B, not an silently imported flat value.

## 6. Relation to reconstruction and remaining scope

The semantic context theorem includes deadlocking and starving operations. A polling certificate alone does not rule out resource deadlock; the strict lock order is independently required. Lock order alone does not rule out starvation; the finite polling bound is independently required. Both are checked against actual primitive protocols, not defined by successful termination.

The reconstruction maps preserve the outer marked trace. To transport this progress theorem, expose the grant/busy/resource/completion marks or the relevant cost/terminal observations in that trace. Their equality transports (E) and other trace-defined properties. It does not manufacture a polling certificate for an arbitrary reconstructed scheduler. The above certificate composition theorem applies to the explicitly retained scheduler contexts and their stated uniform call bounds.

All costs here are root ticks. Routing is finite atomic work inside a tick. Nonzero physical routing overhead needs an explicit additive cost model and corresponding bounds; the products L_iM_ij alone do not bound arbitrary implementation overhead.
