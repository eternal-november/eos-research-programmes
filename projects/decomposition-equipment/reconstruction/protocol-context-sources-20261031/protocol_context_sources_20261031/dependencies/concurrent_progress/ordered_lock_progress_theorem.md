# Concurrent progress from intrinsic service contracts and an implemented scheduler

Scoped derivation, 2026-10-31. This is a sufficient theorem, not a characterization of all concurrent liveness. Resource ordering and scheduling arguments are classical. The intended integration is reuse of the previous two-matrix excursion interface through a richer controlled step/resource cylinder; canonical CFS legs are not stochastic kernels.

## 1. Operational domain and exact restrictions

There are W>=1 fixed worker slots, finitely many mutex resources with a strict total order, and finitely many episode modes i. Entries X_i may be countably infinite. At entry x an episode has countable local state, a genuine stochastic step kernel, and an exposed next action: internal step, acquire a named mutex, release a set of held mutexes, or finish with terminal output / next entry (j,y). A release or finish can be incorporated in a successful local transition. Each state specifies its held set. Acquisitions are permitted only above EVERY resource currently held. Finishing releases ALL held resources. Dormant/terminal slots hold no resources. The only reasons an unfinished worker cannot take its next step are that its requested mutex is owned by another worker; there are no unmodelled conditions, channels, waits, or ownerless locks.

The scheduler rotates deterministically through slots 1,...,W. A slot visit takes one wall-clock tick. If terminal, skip; if requested mutex unavailable, stutter; otherwise perform exactly one local transition, including the atomic resource update. A blocked attempt does not advance the local state/randomness. There is no scheduler fairness premise: this finite cyclic implementation is part of the wiring.

Other workers may delay an episode by holding locks but do not modify its local state or random tape. Shared protected data, if present, must be included in the actual conditional step interface; the autonomous-kernel theorem below does NOT silently permit arbitrary shared-data interference. The robust-control variant requires local inequalities uniformly over the admitted nonanticipating input policies. The manager cannot inspect future private randomness.

This is genuine interleaving with partial resource holdings, NOT serialized whole invocations: distinct workers can execute while holding overlapping subsets of different resources, and one can wait holding a resource while another computes. It is still a restricted protocol: finite fixed worker population, ordered locking, and resource-mediated delay-only interference in the base theorem.

## 2. Intrinsic service contract and conditional past

Ignore availability delays and run one episode's local step kernel. Its intrinsic service duration L is the number of successful local transitions through its finish, including successful acquire/release transitions. This imaginary execution grants requested locks immediately, but still records the resource request/holding trajectory. It is not used to claim the real resources are always available. Allow L=infinity.

For each entry x in X_i, let v_i(x)>=1 finite. Assume

    Pr(L>t | complete past at actual entry i,x) <= b_i(t) v_i(x),  b_i(t)->0;
    Pr(next mode=j | complete past at entry) <= p_ij;
    E[1_next=j v_j(Y) | complete past at entry] <= g_ij v_i(x).

These concern the unconditional intrinsic path law, not the law conditioned on actual completion. Here “complete past” means the revealed interaction/context filtration together with the current entry and outputs of past completed episodes. It explicitly EXCLUDES unrevealed private future tape and any hidden future sample. Conditioning on the latter would invalidate the stochastic contract. Fresh private random tape sampled at entry is a sufficient implementation. The actual granted-step trace is a PREFIX of this latent intrinsic trace: availability affects how quickly the prefix is revealed, not its transition probabilities. This prefix coupling is obtained recursively from the exact local kernels and the nonanticipating scheduler; it is not an extra global progress assumption. Persistent hidden noise must be included in entry state or satisfy the same conditional bounds. Isolated marginals alone are inadequate.

Consequently actual next-entry rewards are bounded by their intrinsic counterparts: on starvation the actual next entry contributes zero, and on completion it is the intrinsic one. All rewards are nonnegative. No conditioning on the event of completion occurs.

Let P=(p_ij), G=(g_ij), and rho(P)<1. No restriction on rho(G) is needed for almost-sure progress. The b_i are local service tails, not wall-clock tails.

## 3. Deterministic scheduler lemma

Every unfinished global configuration has a runnable worker. Otherwise every unfinished worker requests a resource held by another unfinished worker. Follow owner edges. Finite workers force a directed cycle. Along each owner edge, a worker holds the incoming requested resource and requests a strictly larger one, so resource ranks increase strictly around that cycle, impossible. An internal-step worker or a worker requesting a free resource would already be runnable.

In any W consecutive scheduler ticks before global completion, at least one successful local transition occurs. If all W visits failed, no local or manager state changed. A runnable worker at the beginning would therefore remain runnable at its visit, a contradiction. This proves a GLOBAL service bound, not a false bound promising every blocked worker service every W ticks. Starvation freedom is derived below using finiteness of total work, not asserted from cyclic scheduling alone.

If the total number S of successful local transitions needed by all episodes that occur is finite, completion happens within W*S ticks. Indeed if unfinished after W*S ticks, the preceding lemma gives at least S successful transitions. Equality already exhausts all intrinsic service work; an unfinished episode would require at least one further successful transition, contradicting that S is the total required work. Equivalently, on any event with at most B total intrinsic service work and no further episodes, T<=WB. This deterministic implication remains true even if a worker holds locks during arbitrarily long finite computation.

## 4. Concurrent two-matrix theorem

Worker a starts at mode i_a and entry x_a; write v_a=v_i_a(x_a). Let N_a count episodes entered by this worker, including an unfinished episode. N_a=infinity is possible a priori. Let T be wall-clock ticks until all workers terminal, infinity if never.

For m>=1 and t>=1,

    Pr(T > W^2 m t)
       <= sum_a (P^m 1)_(i_a)
          + sum_a v_a [sum_(k=0)^(m-1) G^k b(t)]_(i_a).       (C)

Here b(t) is the column with entries b_i(t).

Proof. At an actual episode entry, the conditional probability of an actual successor in mode j is at most p_ij, since an actual successor is the matching latent successor restricted to the event the episode completes. Thus induction over each worker's entry count gives Pr(N_a>m)<=(P^m 1)_i_a. Likewise induction on nonnegative potential rewards gives the vector inequality for the expected potential at the kth actual entry, bounded by v_a times the i_a row of G^k. The probability any of the first m actual episodes on any worker has latent L>t is therefore bounded by the second term in (C), using conditional tails at its actual entry and a union bound. All entry times are stopping times; defining contributions to be zero when the entry never occurs avoids undefined conditional states.

Outside these bad events, every worker has at most m actual entries and each has intrinsic service <=t. Hence total intrinsic service <=Wmt. The deterministic scheduler lemma forces completion within W^2 mt. This proves (C).

For each fixed m the second term tends to zero as t tends to infinity: finite matrices and a finite sum suffice even if rho(G)>=1. Then let m tend to infinity; rho(P)<1 makes the first term vanish. Therefore Pr(T=infinity)=0. This proves that no worker remains starved and every held resource is eventually released, without a fairness oracle, a finite-state global solver, or a finite-mean premise.

If additionally E[L|entry i,x]<=c_i v_i(x) and rho(G)<1, the same nonnegative entry induction and Tonelli yield

    E T <= W sum_a v_a [(I-G)^(-1)c]_(i_a).

The coarse W factor includes every unsuccessful visit; no hidden scheduling cost is omitted. The wall-clock model assumes each attempt costs one tick and each granted primitive transition costs one tick; variable primitive costs need their own cost labels/bounds.

## 5. Growing countable family

For every W>=2 and resource count r>=2, choose for each episode a nonempty subset H of resources, acquired in increasing order one per local transition. Once all are acquired, retain entry n>=1 and run a nearest-neighbor walk k from n down to 0 with downward probability p>=1/2. On reaching 0, one transition releases all resources and chooses return/termination. A return in mode i yields entry a_i*n in mode j with probability r_ij. Thus local state (mode,n,acquisition index,k,H) is countable and unbounded. At least two workers may use overlapping H (real contention), while additional disjoint H allow computation genuinely concurrently. W, r, subsets, walk biases and entry multipliers vary: this is an unbounded family of countable systems, not a finite-state example repeated.

The intrinsic duration is |H| + walk_hitting_time + 1, up to the declared convention for the first work step. With q=max |H|+1, for t>=q,

    Pr(L>t) <= sqrt(2) n / sqrt(t-q+1).

For smaller t choose b(t)=1 (since v=n>=1). For large t the displayed coefficient defines b(t). Downward bias stochastically dominates the symmetric walk, so this tail also applies to p>1/2. The standard symmetric hitting time is almost surely finite but has infinite mean.

Take two alternating modes, entry multiplier 2, return probability 1/2 each. P has spectral radius 1/2 while G has spectral radius 1. The concurrent theorem still proves AST for every finite W and every ordered resource footprint assignment. With p=1/2 local mean is infinite; with p>1/2 and repeated doubling the aggregate expected service can still be infinite. Thus this family genuinely needs the P/G separation, not merely a finite-mean ranking function.

For finite expected cost choose a_A=a_B=2, return probabilities r_A=3/4 and r_B=1/5. Then G=[[0,3/2],[2/5,0]], rho(G)=sqrt(3/5)<1, and biased walks p>1/2 yield the cost theorem with c_i large enough to cover lock overhead plus n/(2p_i-1).

## 6. Exact role of reconstruction

The old isolated marked duration/output kernel does not expose the resource request/holding trajectory. It cannot verify ordered acquisition and cannot determine how scheduling delays interact with local execution. A step/resource cylinder must retain enough controlled finite-history tests to recover the actual conditional transition law, next requested resource, resource releases, completion and typed reentry. The controlled-prefix companion establishes the exact operational context-substitution bridge for this richer interface.

Concrete encoding into the companion controlled-prefix interface: expose the pending action (internal, acquire r, release H, finish) before its scheduler visit; the manager input reports grant/busy and any admitted resource observation. The output marks the performed action, new held set, released set, terminal/reentry outcome and primitive tick cost. Manager state records resource owners and checks that held-set updates, releases and cleanup agree. An acquisition and its grant/busy reply are one atomic transaction in this core convention; any two-phase implementation must instead count its phases explicitly and rederive the timing constant. No hidden unbounded computation is permitted inside a tick. The controlled tests retain the initial preparation/entry, all these transaction prefixes, and reentry labels. Therefore their equality preserves the resource protocol and tick granularity, not only eventual returns.

The numerical certificate rows remain the old P/G/service-tail evaluations on intrinsic episode paths. They are derived from the step cylinder, not extra magically executable CFS legs. If a positive normalized realization preserves that controlled cylinder and stays inside the same resource protocol, the local conditional prefix law and inequalities are unchanged, so theorem (C) transports. Compatible cylinder comparison spans preserve the named scalar tests. Formal Isbell/CFS existence alone does not imply a physical realization, an executable canonical apex, or preservation of resource protocol.

The strength/limitation is explicit: this proves a new DOMAIN OF REUSE for the preceding progress interface under classical resource/scheduler hypotheses. It does not establish novel general concurrency theory or solve arbitrary interfering concurrent programs. Spawning is outside this core result. External arrivals, resource-owner failure, arbitrary shared-state mutation and non-ordered lock acquisition require additional interfaces/proofs, not silent extrapolation.

## Coherence convention

Reassociation/regrouping retains the SAME global worker-slot cyclic order, manager state and primitive tick granularity. A hierarchical round-robin scheduler is generally a DIFFERENT context and need not preserve either trace law or the W factor. Formal coherence does not license silently changing the scheduler. In the history-state reconstruction a blocked/busy observation may enlarge the recorded history; it need not literally leave the reconstructed history state unchanged. The required stuttering fact is semantic: erasing unavailable-acquisition visits leaves the same intrinsic successful-grant law and resource protocol. This is preserved by equality of controlled-prefix cylinder entries plus the stipulated nonanticipating conditional closure.
