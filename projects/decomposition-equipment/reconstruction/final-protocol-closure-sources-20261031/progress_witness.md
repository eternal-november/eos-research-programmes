# Variable-duration nested-call progress witness

Constructive companion, 2026-10-31. Scoped to the small-step language, not a claim that arbitrary compound calls terminate. Standard random-walk, ordered-lock, union-bound and nonnegative-matrix arguments are used openly.

## 1. Operational clock and ownership

There are W>=1 worker slots, each with a finite current call stack and countable frame states, and finitely many totally ordered mutexes. A round-robin root scheduler selects one worker per microtick. Exactly one primitive instruction of its top frame executes: local work, CALL/push, RETURN/pop, acquire, release, or terminal decision. Every such instruction costs one microtick. CALL only pushes/initializes the child frame and does not execute its body; RETURN only pops/delivers the result and does not execute the caller continuation. The next body/continuation instruction requires its own later scheduled microtick. The current pending action, running/return status and resource effects are exposed by the microstep boundary. A failed acquire costs a tick but does not advance intrinsic state or consume private randomness. An already terminal worker is an absorbing no-op; padding is only for analysis.

The caller suspends after CALL. Other worker stacks remain schedulable. All frames of one worker inherit the same worker ownership identity, and only the single root manager changes mutex ownership. An acquisition is permitted only if its resource is strictly above every resource currently held by this worker; therefore recursive reacquisition of an already held lock is not permitted. Release and successful acquisition are reported immediately at that microtick, not bundled with eventual return. A RETURN does not fabricate release: explicit releases or the specified final cleanup policy govern resources. The witness below explicitly releases everything before termination.

No ancestor performs an uncharged computation: transparent routing only exposes the chosen top instruction. Terminal workers hold no resources (explicit releases before termination, or an explicit atomic final-cleanup instruction). No worker can be blocked except by an attempted acquisition of another worker's mutex. In particular there is no cross-worker join/await. Every local/internal/CALL/RETURN instruction is runnable, even if it might lead to an infinite sequence. These are checkable syntax and ownership conditions, not termination assumptions.

## 2. Deterministic service lemma

In every unfinished reachable configuration some unfinished worker has a runnable top instruction. Otherwise every unfinished worker waits for another owner. Following owner pointers in this finite worker set yields a cycle. On a wait edge a->b, the lock a requests is held by b; if b is also waiting, b's requested lock is strictly larger. A cycle would yield a strict cyclic increase, impossible.

If a length-W interval contains no successful primitive instruction, all intrinsic worker states, stacks and ownership remain unchanged. A worker runnable at its start remains runnable until its round-robin slot, where it must execute successfully, contradiction. Thus every full W-tick interval preceding completion contains at least one successful instruction. This is a GLOBAL service bound, not a per-worker success or per-compound-call return bound.

More generally a scheduler with a uniform B-microtick polling envelope for every worker has the same lemma with B instead of W, provided the envelope counts actual microticks, including all call administration. Do not reuse an envelope measured in completed calls.

## 3. Explicit growing family with intermediate resource effects

Choose W>=1, R>=2 resources, finite depth d>=1, positive entry n, and two modes A,B. Each worker is assigned two distinct resource indices l<h; arbitrary overlaps are allowed. For W=R-1 a concrete growing choice is worker a assigned (a,a+1). This gives genuine contention without requiring every worker to share one global mutex.

The initial configuration has each root frame already ready at its declared initial episode entry (i,n); T starts there. The authoritative manager initially marks every mutex free and each worker held-set empty; every episode reentry also has empty held-set after the preceding explicit releases. External initialization/START instructions, if included in a mission, must contribute their explicitly charged elapsed time in addition to the bounds below. Reactivation is a single charged tail-transition which reuses the persistent root frame, updates its mode and entry and resets its program counter; it is not an uncharged root CALL/RETURN pair. All actual child CALLs and RETURNs remain separately charged.

The source routine tree has finite depth d in each family instance. Its run-time stack is the current finite root-to-active-leaf chain, of depth at most d+1; source-tree substitution depth is not an assertion of arbitrary recursive/dynamic stack closure. The family grows with d, but no invocation dynamically creates a deeper routine than its fixed source tree.

One episode at mode i and entry n does:

1. acquire l, then h;
2. CALL the left depth-(d-1) binary routine;
3. release h, immediately visible to the manager and other stacks;
4. CALL the right depth-(d-1) binary routine;
5. release l;
6. make one final terminal-or-reactivation decision: switch to the opposite mode at entry 2n with probability r_i, otherwise terminate.

An internal binary routine of depth k>0 sequentially CALLs two depth-(k-1) routines, then RETURNs. A depth-0 leaf keeps k=n and takes fresh nearest-neighbor random-walk steps until k=0 (down probability p_i>=1/2), then RETURNs. Each walk step, CALL, RETURN, acquire, release, and final decision is a separate successful instruction. All leaf calls receive the same episode entry n; fresh private innovations are used on each walk and reactivation. Suspended callers retain their locals and locks. This is a real nested, multi-call protocol, not a completed-call kernel pretending that locks are invisible during execution.

Let q=2^d be the leaf count. If all attempted acquires were immediately granted, episode intrinsic length is

    L_i(n) = H_1(n)+...+H_q(n)+C_d,   C_d=4q+1.

Verification of overhead: a depth-k binary routine costs 4*2^k-3 non-walk instructions (leaf RETURN=1, recursion A_k=2A_(k-1)+3). The episode has two routines of depth d-1 plus 2 root CALLs, 2 acquisitions, 2 releases, and 1 decision: 2(4*2^(d-1)-3)+7=4q+1. Failed acquire ticks are NOT in L; they are covered by the service multiplier. Active stacks have bounded depth d+1 here, while their states and durations remain countably unbounded. W, R, d and n are arbitrary finite family parameters.

The release of h separates two potentially unbounded subcalls while l remains held. Thus intermediate resource prefixes are essential even in this positive family.

## 4. Derived local certificates, including nonreturn

Write v(n)=n. The standard reflection bound for a symmetric walk, and downward-bias coupling, give

    Pr[H_j(n)>s] <= sqrt(2)*n/sqrt(s+1),    p_i>=1/2.

In particular this proves H_j<infinity almost surely; it is not an assumption. Set for integer t>=0

    b_d(t)=1,                                      t<C_d,
    b_d(t)=min(1, q*sqrt(2)/sqrt(floor((t-C_d)/q)+1)), t>=C_d.

Union bound (independence is not needed for this step) gives Pr[L_i(n)>t]<=n b_d(t), and b_d(t)->0. The minimum with1 is valid since both probability<=1<=n and the displayed union bound hold. This derives episode intrinsic almost-sure termination, including all nested calls and administrative work.

The reactivation decision gives P_AB=r_A, P_BA=r_B and G_AB=2r_A, G_BA=2r_B; other entries vanish. If p_i>1/2, then

    E L_i(n)=q*n/(2p_i-1)+C_d <= c_i n,
    c_i=q/(2p_i-1)+C_d.

For p_i=1/2, E H_j(n)=infinity, so E L_i(n)=infinity even though its tail tends to0.

Fresh independent private randomness and boundary-only delay interference give these bounds conditionally on the actual complete past at each episode entry. No future tape, hidden descendant state or post-return information is included in that conditioning. A latent intrinsic episode can be sampled at entry and consumed only on successful instructions. The actual execution is its prefix; delays do not alter its next transition. Sampling an entire countable trajectory is a mathematical coupling device, not an algorithmic exact-sampler claim.

## 5. Derived concurrent completion theorem

For worker a, let (i_a,n_a) be its initial mode/entry. Let T be root microticks until all workers terminate, with T=infinity on nontermination. Actual episode entries include entered-but-unfinished episodes. Under the preceding ownership/service conditions, for m>=1 and t>=0 integers,

    Pr[T > B*W*m*t]
      <= sum_a (P^m 1)_(i_a)
         + sum_a n_a [sum_(k=0)^(m-1) G^k b(t)]_(i_a),             (1)

where b(t)=(b_d(t),b_d(t)) and B=W for root round-robin.

Proof: the probability that worker a starts more than m episodes is bounded by (P^m 1)_(i_a). Conditional latent exit indicators dominate actual successor entries even if scheduling prevents return; never condition on successful return. The expected active entry-potential vector at its k-th entry is bounded by n_a e_(i_a) G^k. Union-bound the event that any of its first m entered episodes has FULL latent L>t, including an unfinished episode. Outside these bad events there are at most Wm entered episodes and their total latent successful work is at most Wmt. If execution remained unfinished longer than B Wmt ticks, the service lemma would force more successful instructions than that finite budget permits. This proves (1); the t=0 case is trivial from the tail bound.

If rho(P)<1, first choose m large and then t large. Equation (1) proves T<infinity almost surely. No rho(G)<1, bounded duration, or finite expected duration was required. In particular take r_A=3/4, r_B=1/5 and symmetric leaf walks: both real call-return and total concurrent mission completion are derived, but E T=infinity. Each initial leaf alone supplies the infinite-mean lower bound.

If additionally rho(G)<1 and the finite-mean c bounds hold, nonnegative summation gives

    E T <= B * sum_a n_a [(I-G)^(-1)c]_(i_a).                    (2)

This includes complete latent costs of entered episodes; it never erases a blocked unfinished episode. For r_A=3/4,r_B=1/5, rho(P)=sqrt(3/20)<1 and rho(G)=sqrt(3/5)<1. If p_A=p_B=2/3, q=2^d and C_d=4q+1, then c_A=c_B=7q+1. Since [(I-G)^(-1)1]_A=25/4 and the B entry is7/2, (2) becomes

    E T <= B*(7q+1)*( (25/4) sum_(a:i_a=A)n_a
                              +(7/2) sum_(a:i_a=B)n_a ).

This bound is conservative because administrative overhead was absorbed into n. It concerns the concrete concurrent implementation, not a reconstructed formal apex.

## 6. Necessary boundaries and valid failure cases

A. **Nested self-deadlock without inherited ownership/order.** A caller acquires lock l, calls child, waits synchronously. If child is treated as another owner and needs l, parent waits for child while child waits for parent. Both standalone routines can terminate. Syntactic nesting does not imply the mutex-only wait-cycle proof applies; the ownership and no-cross-worker-await restrictions are doing real work.

B. **Opposed acquisition order.** Two workers take l then h versus h then l under RR. After two acquisitions both wait forever. Their isolated successful duration/exit laws can match the common-order case. The language admits the bad context; it simply lacks this progress certificate.

C. **Infinite activity while holding resources.** A child executes an endless local loop, never RETURNs, while its caller holds l. Its prefix semantics is valid and observes ownership persisting. Another stack can forever receive busy on l. The scheduler remains fair and global service may continue, but L=infinity and b(t)->0 fails. A completed-return-only summary that silently renormalizes finite returns is false.

D. **Local return does not imply global completion.** Set r_A=r_B=1 and p_i>1/2. Every episode returns/re-enters almost surely, and every call is finite, but the worker never terminates. Here rho(P)=1 and no terminal event occurs.

E. **Starvation by an explicit no-call context.** A root controller can forever perform its own local ticks and never dispatch an unfinished worker. It is valid small-step semantics. It lacks finite B; no progress follows merely from child termination. A root that stops polling is not padding for a terminal mission.

F. **Hidden release timing changes composition.** A controller holding h can release before a long child call or after it. Both can have the same eventual duration and final returned state, but another worker's acquire outcome during the call differs. The boundary must retain resource events at their times; endpoint duration alone does not preserve concurrent observations.

G. **Clock substitution is not free.** Treating a compound CALL as one tick would replace q unbounded walks and 4q+1 administrative instructions by a unit cost, invalidating (1)-(2). Infinite zero-time administrative behavior is excluded by the one-instruction/one-microtick language, not erased from a richer language.

These are failures of particular hypotheses/interfaces, not universal impossibility of completing the underlying mission by some different policy. For example serializing whole calls may repair opposed lock acquisition but changes the scheduler and observations.

## 7. Link to reconstruction and stopping scope

Use the main theorem's exact microstep controlled-prefix reconstruction, with start/resume/return/effect observations, retaining the actual scheduler and sole manager. Equality of its finite timed/resource prefixes preserves the event T<=N at each finite N (include terminal marks). Therefore it preserves all completion tails and, by nonnegative summation, E T including infinity. It also preserves every resource-safety predicate measurable on finite prefixes. This is a boundary-law conclusion; no stochastic interpretation of canonical cylinder-factorization apex or span legs is needed.

The separate common-cylinder normalizer comparison and its coherence are supplied by the main construction, not inferred from this numerical progress lemma. No arbitrary intervention theorem is claimed here: interventions changing locks, scheduler or worker transitions must be admitted by that operational language and must independently preserve these certificate hypotheses for these numerical bounds to remain available.

This discharges the positive growing-family gate and supplies operational counterexamples for the final bounded workstream. It does not extend to spawning, arbitrary cross-worker joins, hidden shared mutation, arbitrary real-time costs, or unrestricted feedback; those are documented limits rather than further workstream targets.
