# Acquired shared-priority evidence transports anonymous role certificates

31 October 2026. A scoped operational theorem with an exact polynomial poset certificate, a strict improvement over marginal assignment matching, and a growing local-information obstruction repaired by costed joint experiments.

## 1. What is preserved, what is acquired, and what changes

Known addressed modules expose FIFO queues and actual invocation payloads. A local certificate specifies intrinsic service work, FIFO order, and reliable callback behavior **conditional on resource grants**. It does not promise isolated wall-clock latency in every context. Wiring connects the queues to one known exclusive unit-rate server. The missing contextual fact is its persistent strict module-priority order, not its existence or capacity. Joint timing experiments acquire comparisons of that order; the theorem derives their consequences for anonymous report association.

The ingredients—priority scheduling, trace refinement, sorting, partial orders and adjacent-swap arguments—are standard. The specific result combines operational acquisition with an exact payload-sensitive certificate retaining joint precedence constraints. It is not a general new composition calculus or a claim that service-demand conservation can be learned from finite experiments.

**Explicit interface change.** For the constructive acquisition/repair family, each module has a fast productive operation P_i and a slow safe diagnostic operation D_i. These are two known addressed operations sharing its FIFO. Selecting an operation changes service demand, not its uncontrollable payload. This is richer than a model with only one fixed operation per module. Failure and repair use the same newly declared interface; they do not claim unchanged hardware relative to a previous single-operation model. The sharp obstruction uses a coarse request grid with one atomic batch commit per tick. Section 7.1 separately proves a weaker growing-family obstruction when multiple same-tick commits are permitted; the n=2 obstruction does not survive that richer API. No callback tags, payload pilots, reference sensors or new production-time observations are added by repair.

## 2. Primitive semantics and separately learned contracts

An invocation j has public address, release r_j and known physical role rho(j). It requires intrinsic work d_j>0. Once granted, it occupies the exclusive server nonpreemptively at unit rate for d_j; ungranted waiting consumes no intrinsic work. Wiring does not change d_j or FIFO order. A completed invocation emits exactly one callback with its bit and lag in [0,J]. The public callback contains only arrival time, bit and raw-stream occurrence: no address, invocation identity, source, service start or grant metadata. Payloads, work and lags need not be independent for the positive theorem.

Unit-rate dedicated calibration from a certified empty queue can establish sound work intervals. A singleton callback at elapsed a_j gives

    L_j=max(0,a_j−J),    U_j=min(D_j,a_j),    d_j in [L_j,U_j],

when D_j is an independently supplied upper bound. Fixed-demand repeatability between calibration and production is a supplied primitive. More general sound intrinsic-work sets may replace intervals. Separate calibration cannot prove that contention leaves intrinsic work unchanged; hardware with context-dependent work requires a different contract. Correlated actual local parameters are allowed, since their actual tuple belongs to the product of sound marginal contracts. Any stronger retained joint parameter constraint must also be preserved.

The server is work-conserving and chooses the highest-priority ready module whenever it becomes idle. Priority pi is one unknown strict permutation, persistent across the specified diagnostics and production. Payloads do not affect arbitration. Initial emptiness or an independently bounded drain, reliable clock/release operations, safe no-actuation diagnostics preserving work/arbitration, finite arithmetic/storage, and a physical role-load bridge are supplied capabilities. Under that bridge the required command for role a is the XOR of the bits of its actual productive invocations. Safe isolation and retention leases cover all waiting, output and final tails. These physical facts are not inferred from anonymous timing.

The batch results use exactly one required productive job per module. Atomic batch admission queues the entire batch before the idle-resource arbitration decision. For the negative/repair family the API additionally permits **at most one atomic batch commit per legal grid tick**, enforced across all callers. This prevents sequential same-tick singleton commits from starting a chosen job before its competitors are admitted. This is a supplied, restrictive and costed admission-before-dispatch capability; separately processed enqueue calls sharing a numeric timestamp do not suffice. Multiple all-ready jobs per module yield priority blocks and require a different combinatorial model.

### Derived service and arrival order

For a general finite request log, after m completions let c_m be the previous completion and H_m the first unserved job in each nonempty module FIFO. If work remains, primitive semantics force

    s_(m+1)=max(c_m,min_{j in H_m} r_j),
    A_(m+1)={j in H_m:r_j<=s_(m+1)},
    j_(m+1)=the highest-pi-priority module head in A_(m+1),
    c_(m+1)=s_(m+1)+d_(j_(m+1)).

An empty ready set forces waiting; a nonempty ready set forbids idle time; nonpreemption gives the final equality. Thus contextual completion behavior is derived from grants and arbitration, not assumed equal to isolated behavior.

For a simultaneous all-ready batch at t=0 this reduces to

    c_k=sum_(h=1)^k d_(pi_h),     arrival_(pi_h)=c_h+delta_(pi_h).

If every learned lower bound satisfies L_j>J, then successive arrivals differ by at least L_(pi_(k+1))−J>0. Therefore **raw callback rank equals service priority rank** on this batch. No persistent anonymous rank was supplied; this dynamic rank fact follows from the primitive semantics and learned bound. A closed horizon sum_j U_j+J, reliable counts, and absence of carry-in/out establish one actual global bijection from jobs to these n report occurrences.

For arbitrary releases, service-order branches may depend on uncertain durations. Retaining all feasible recurrence branches is sound; choosing one nominal order need not be. No generic polynomial exact analysis of those branches is claimed. The theorem below uses the batch specialization.

## 3. Shared evidence and the transport object

Let P be an acyclic strict partial order of acquired priority comparisons on the n modules. Every recorded comparison must be proved sound for the same persistent pi. Therefore the actual pi lies in LE(P), the set of linear extensions. Cycle detection precedes certification; a cycle is model/evidence inconsistency, never vacuous success.

For report bits b_1,...,b_n in their observed rank order define

    V_a(sigma,b)=XOR_{k:rho(sigma_k)=a} b_k,   sigma in LE(P).

Operational rank derivation proves that the actual physical role vector is V(pi,b) for one common pi in LE(P). This is the transported joint-assignment coverage statement. It does not choose separate favorable job identities for different reports or roles.

The abstraction LE(P) may ignore constraints from exact production timestamps, shared work parameters or richer diagnostic records. Universal agreement on LE(P) remains sufficient. Disagreement is only UNRESOLVED unless the conflicting extensions also reproduce the full retained evidence. Thus the exact certificate below is exact **for the poset abstraction**, not automatically complete for every physical trace.

## 4. Exact payload-sensitive certificate

For incomparable modules x,y, let Pred(x),Succ(x) be strict predecessor/successor sets in P and define

    D_xy=Pred(x) union Pred(y),    U_xy=Succ(x) union Succ(y),
    a_xy=|D_xy|+1,                z_xy=n−|U_xy|−1.

Ranks use indexing 1,...,n.

**Adjacent-rank lemma.** There is a linear extension placing x,y consecutively at ranks k,k+1, in either order, exactly when a_xy<=k<=z_xy.

Necessity follows because all D_xy precedes their block and all U_xy follows it. For sufficiency, D_xy is a downset and A=V\(U_xy union {x,y}) is a downset containing it. Starting with D_xy, append prefixes of a topological order of A\D_xy. This yields a downset I of every size from |D_xy| through |A|. Choose |I|=k−1. Both x and y are then enabled, and may be appended in either order because they are incomparable. Complete the suffix topologically. This also constructs the two extensions.

**Exact certificate theorem.** The vector V(sigma,b) is constant over all sigma in LE(P) if and only if every incomparable cross-role pair x,y satisfies

    b_k=b_(k+1) for every k in [a_xy,z_xy].                 (C)

Swapping adjacent incomparable x,y at ranks k,k+1 changes V by

    (b_k XOR b_(k+1)) (e_(rho(x))+e_(rho(y))).

A violated test therefore constructs two genuine linear extensions with different role vectors. Conversely, any two linear extensions are connected by adjacent incomparable swaps: move the desired first element leftward through the current order, crossing only incomparable elements, fix that prefix and repeat. Under (C) every such swap has zero vector difference. This proves both directions.

A passing certificate computes V using any one topological order. By §3 that vector is the actual required physical command. A failed certificate returns two poset-feasible assignments and UNRESOLVED; a physical impossibility statement requires additional realizability evidence.

### Finite implementation and uniform specialization

Transitive closure, acyclicity and all predecessor/successor unions can be computed in O(n^3) elementary Boolean/index operations. Precompute prefix sums of t_k=[b_k!=b_(k+1)]; every interval test is then constant-time. Storage is polynomial, with O(n^2) reachability bits plus indices, role labels, payloads and witness orders. Actual index/label lengths and integer arithmetic are charged. An independent checker verifies the poset, orders, interval tests and output. Complexity is not a hardware latency guarantee: implementation bounds must pay these operations.

For a fixed acquired P, intervals may be compiled before production. Per-burst transition-prefix construction, O(n^2) tests and role aggregation have a separate charged bound. If the uniform specialization below passes during compilation, per-burst binding can instead use its fixed role-by-rank word and O(n) aggregation.

Condition (C) holds for every bit word if and only if every incomparable pair has the same role. Sufficiency follows from same-role swaps. Necessity follows because every incomparable cross-role pair has a nonempty feasible adjacent interval; choose a bit transition there. Equivalently, every remaining priority has the same role word (rho(sigma_1),...,rho(sigma_n)). This is the exact task-relative quotient of latent priority for uniform arbitrary-payload completion: within-role identity may remain unknown.

## 5. Strict improvement over marginal assignment matching

Let jobs be 0,1,2,3, with acquired comparisons 0<3 and 1<2, roles (A,B,A,B), and observed rank bits (0,0,1,1). The six linear extensions are

    (0,1,2,3), (0,1,3,2), (0,3,1,2),
    (1,0,2,3), (1,0,3,2), (1,2,0,3).

All give role parity (1,1), so the exact certificate accepts. Even the exact marginal possible rank sets are {1,2,3} for jobs 0,1 and {2,3,4} for jobs 2,3. Their bipartite compatibility graph admits the impossible order (0,2,1,3), yielding (0,0). Thus an all-perfect-matchings checker on this marginal graph correctly returns UNRESOLVED, while the precedence-preserving checker certifies. The difference is retention of joint precedence constraints, not a hidden tag.

This example is physically realizable. Use the fixed fast/slow interface of §7 and retain only pair diagnostics establishing 0<3 and 1<2. Each pair's entire timing distribution depends only on that tested comparison; all six priorities reproduce the full diagnostic record with suitably coupled allowed probe bits. Equal productive demands Q and zero jitter give the same productive timestamps (Q,2Q,3Q,4Q) for all six. The displayed bit word is a permitted realization, and every feasible physical role vector is (1,1).

More generally a failed poset certificate has a physical two-world witness when both constructed extensions and common feasible productive demands tau reproduce the **entire retained record**, and payload laws permit the common observed word. Common tau in marginal intervals alone does not ensure this. Exact timestamps or additional joint evidence can remove an extension; they may not be silently forgotten when asserting impossibility.

## 6. Wiring, refinement and substitution

Disjoint groups may possess sound local priority evidence P_i. Reuse requires those comparisons to constrain the restriction of the same persistent global priority, not an unrelated local arbiter. Cross-group experiments contribute E. Combined evidence is

    P=transitive_closure((union_i P_i) union E),

with cycles rejected. Every actual common priority extends this union. Union and transitive closure are insensitive to record grouping, so regrouping the evidence yields the same LE(P). This gives an elementary coherence law with one shared latent witness; independently selecting a favorable priority per subgroup is invalid.

If sound evidence refines P to P', then LE(P') is a subset of LE(P). Consequently a certificate for a fixed batch, roles and observed bits remains sound after refinement. More evidence can enable previously unresolved words. Adding jobs changes service ranks and requires recomputation; no acceptance-monotonicity claim spans changed batches.

Intrinsic-work substitution also has a precise limited law. If every work/output transition history of a replacement component belongs to the old component contract, with unchanged FIFO/callback interface, role bridge and scheduler, replaying any new execution in the old contract gives the same scheduler choices and observations. Hence contextual trace inclusion holds. If old analysis used stronger cross-component parameter constraints, replacements must preserve those too; marginal refinement alone is insufficient. In the batch theorem retain L_j>J to preserve the rank derivation. Changes to actual arbitration, resource count, roles, physical bridge or admission order require new proofs.

Grouping components while retaining the same single server and global labels is harmless renaming. Adding per-group schedulers or cloning capacity is a different physical wiring, not covered by this coherence statement. Local chains can be merged by cross-group comparisons using standard algorithms; their costs are real, and internal comparisons need not be relearned.

## 7. Growing valid-local / failed-global family

Fix n>=2 and Q>0. Each module i has P_i of fixed demand Q and D_i of fixed demand 2Q. J=0; every invocation's payload is an uncontrollable fresh independent fair bit. Productive roles are distinct, one per module. The single server's unknown pi can be any of n! priorities. All local FIFO/work facts are correct in all worlds.

Every adaptive calibration that never leaves work pending in two modules at once is pi-blind: durations depend only on that chosen module, and callback bits are iid fair. Couple bits by public occurrence to obtain identical complete histories, including adaptive stopping. Arbitrarily extensive isolated/fully drained learning does not reveal priority. This is not a prohibition of joint experiments: those are the repair below.

Let the legal request grid have quantum R=nQ. Required fresh productive jobs become available at relative time zero, and may not be prefetched, substituted or rerun. At most one atomic batch commit is legal at each grid tick, with capacity for all n productive requests. The externally fixed deadline is

    H=nQ+gamma,             0<gamma<Q,

where gamma includes supplied bounds for readout, assignment/checking, commands, actuation and required final tail. Q or hardware provisioning must make this real bound possible; arithmetic is not instantaneous.

Any useful job first admitted at the next legal tick R completes no earlier than R+Q>H, so all must admit at zero. The one-commit-per-tick rule forces all required jobs into the SAME atomic batch, queued before the first arbitration decision. Merely supplying an optional atomic-batch operation would not prove this: multiple same-tick singleton commits could impose a known first job and defeat the n=2 obstruction. The required jobs occupy nQ service. Any extra complete invocation ahead adds at least Q and misses the deadline. If calibration backlog is allowed, grid admissions and demands Q or 2Q force service endpoints onto Q multiples; positive residual work at zero is at least Q and also defeats completion. Jobs queued behind the productive work cannot yield an extra completed report by H. A certified empty start avoids this residual argument entirely.

For the productive-only execution, reports arrive at Q,2Q,...,nQ regardless of pi. Use that execution as a virtual extension to every priority, including worlds where a policy's extra work causes failure. Every actual successful world has the same productive record as its virtual execution; counting extra virtual successes can only raise the upper bound. Under uniform pi and fair virtual productive bits, a rank word containing k ones induces a uniformly unknown role vector among binomial(n,k) possibilities. For each such public successful record the common policy proposes one output, so actual successful worlds are at most the reciprocal fraction of these virtual worlds. This argument does not condition on actual success and then assume uniform priority. Thus

    average_pi success <= sum_(k=0)^n (binomial(n,k)/2^n)/binomial(n,k)
                       = (n+1)/2^n.

Some fixed world therefore has combined missed/unsafe risk at least 1−(n+1)/2^n. A uniform private priority guess attains that risk in every world but is not hard-safe. For a productive-only manifest (no additional diagnostic/calibration work during production), a hard-safe policy can complete only all-equal words, with probability 2^(1−n). This exact hard-safe comparator is not asserted for policies deliberately adding extra work to filter which priority worlds meet the deadline. The combined-risk bound above continues to include such extra-work policies. Refusal and missing useful work count as failure. A pi-informed controller using identical hardware and no future payload information completes every realization by H.

This is a local-information obstruction, not an all-legal-experiment lower bound. The coarse primitive grid and one-commit-per-tick restriction are essential to this SHARP bound: arbitrarily fine free staggering or multiple independently dispatched commits at one tick can defeat it. The following subsection treats multiple same-tick commits separately rather than claiming the sharp bound for that richer API.

### 7.1 Relaxed admission API: multiple commits at the same grid tick

Retain the same physical work, freshness, priority, grid R=nQ and deadline, but allow arbitrarily many sequential atomic commits at a single tick, dispatching immediately after each commit if idle. This is a strictly richer API. The positive batch certificate and joint-probe repair remain valid when the controller chooses one batch; the sharp preceding risk bound is replaced below.

All useful jobs still must be admitted at time zero. No callback occurs before Q, so no same-tick admission decision can depend on a fresh callback. Giving the controller zero-cost sequential commits only strengthens it. Conditional on its local calibration history and private random seed, let S be the first nonempty admitted productive subset, of size s. Its highest-priority member starts immediately. All other required jobs must be queued during that first service, at the same tick, and their later service order is their restriction of pi. Thus on every successful execution the actual productive service permutation is

    sigma=f_S(pi)=[min_pi S] followed by pi with that winner removed.

Strategies introducing completed nonproductive work before all useful jobs finish miss the deadline. For counting combined success, extend each such unsuccessful world virtually to its productive-only f_S order: counting additional virtual successes only increases an upper bound. On every successful world the actual completed report word and service order equal this virtual productive-only execution. Its public callback times are Q,...,nQ, so a common policy has one response to each successful bit word, even if extra queued work makes some other worlds fail. Later commit partitioning cannot affect the successful remaining priority order. Extra-work failure can, however, filter posterior priority support conditional on successful timing; it must not be ignored when asserting an exact hard-safe optimum. Choices of S may be randomized/adaptive to local histories, but those histories are pi-blind, so conditioning on them leaves uniform pi.

If s=1 the first productive identity is known, while the remaining n−1 identities occur in uniform unknown order. The same payload-count calculation as above, on that tail, gives optimal combined success

    n/2^(n−1)=2n/2^n.

In particular n=2 is fully solvable by same-tick sequential singleton commits. It must not be advertised as an obstruction under this relaxed API.

For s>=2, each service permutation sigma has at most n−s+1 preimages under f_S. To see this, its first element must lie in S; remove that winner from sigma and reinsert it into a possible latent pi strictly before the earliest remaining S member. Since the remaining s−1 members occupy distinct positions, there are at most n−s+1 insertion positions. All other elements retain their relative order.

For the counting argument, define a hypothetical productive-only execution f_S(pi) for EVERY latent priority, including those where actual extra work causes failure. Its iid fair rank-bit word y is independent of pi, including under the nonuniform distribution of f_S(pi). On every actual successful execution this virtual word equals the actual complete productive record. We count successful actual worlds as a subset of these virtual worlds; we never condition on actual success and then assert that pi remains uniform. For a word with k ones and any proposed role vector, exactly k!(n−k)! unrestricted permutations assign that word to that vector. Consequently at most (n−s+1)k!(n−k)! latent priorities can make the proposal correct, and conditional success is at most (n−s+1)/binomial(n,k). For k=0,n use the exact upper bound 1. Averaging gives

    success <= [2+(n−1)(n−s+1)]/2^n
            <= [2+(n−1)^2]/2^n,             s>=2.

Averaging over choices of S therefore proves the valid, not claimed optimal, bound for every local-information-only policy under the relaxed API:

    average_pi success <= max(2n,n^2−2n+3)/2^n.             (R)

For n>=3 this is strictly below one and tends to zero exponentially. Some fixed priority world has missed/unsafe risk at least one minus (R). Unlike the sharp one-commit formula, no equality/optimality claim is made for this relaxed combined-risk upper bound.

For the productive-only production manifest, with no additional diagnostic/calibration work queued during production, the optimal hard-safe completion probability is 2^(2−n). For a singleton S, the known first bit is unrestricted while all remaining bits must agree; that event has probability 2^(2−n) and permits a correct command. For s>=2, the support of f_S contains every permutation starting with any member of S (take pi equal to that permutation). Fixing a first member lets all tail identities permute, forcing tail bits to be constant for a hard-safe command. Choosing a different first member of S then forces the first bit to equal that common tail bit. Hence only all-equal words are safe in that case. Randomization cannot improve this productive-only singleton strategy's hard-safe bound. With extra work allowed, some priority worlds can be selectively forced to miss the deadline; successful timing can then filter their support. The exact hard-safe optimum is not established for that larger class. Only the combined success bound (R) above is claimed for arbitrary extra-work policies. Refusal continues to count as missed work.

This establishes a growing failure of local-only evidence even without the one-commit restriction, while acknowledging the stronger controller and its successful n=2 workaround. It still relies on the coarse admission grid; arbitrarily fine staggering is not covered.

## 8. Safe acquisition and fully charged repair

From drained idle atomically admit D_i (2Q) and P_j (Q), i!=j. Callback times are (2Q,3Q) if i outranks j and (Q,3Q) otherwise. The first arrival identifies the comparison without identifying either payload. Both operations already exist in the declared interface, and safe probing preserves the same arbitration law. Total probe service/horizon is 3Q.

All m=binomial(n,2) comparisons suffice to recover pi with a consistency check. Standard adaptive comparison sorting can instead use a conservative m<=n ceil(log2 n) bound. A concrete mission-aware strategy repeatedly selects any incomparable pair with different roles, performs its slow/fast comparison, inserts the observed directed edge and recomputes closure. Every insertion is sound for the actual priority, so it cannot create a cycle under the premises. The chosen pair becomes comparable permanently. With n_a jobs of role a, the algorithm therefore stops within the predeclared bound

    m_max=sum_{a<b} n_a n_b,

or within the smaller number of initially incomparable cross-role pairs. At termination all incomparable pairs have the same role, so the uniform certificate theorem proves readiness for every subsequent productive bit word. Within-role priority need never be resolved. This is a sufficient algorithm, not an optimal comparison strategy. Reserve m_max probe slots before observing outcomes; if the algorithm finishes earlier, waiting to the fixed T0 remains charged. Choosing between this bound and a total-sorting bound can likewise occur before observations. Particular observed words may be accepted earlier by (C), but that alone gives no uniform mission-completion guarantee over future payloads.

Let C_init bound justified initial drain/setup, rho_probe the physical post-probe tail, C_probe callback handling, exact comparison, dispatch preparation and endpoint guards, and C_compile evidence consistency, order/interval construction and production readiness. For the adaptive mission-aware algorithm, C_probe additionally includes selection and closure updates after each comparison (for example O(n^3) elementary operations with the simple implementation); they are not deferred for free. Pre-observation budgets use independently supplied work caps D_P>=Q and D_D>=2Q. Define H_pair=D_P+D_D; these caps and hardware costs determine the commissioning reservation before any observations. If exact local facts are explicitly sunk, H_pair=3Q is available; publicly supplied fixture caps Q,2Q likewise give this value without an oracle for unlearned work. With R=nQ reserve

    S_init=R ceil(C_init/R),
    S_pair=R ceil((H_pair+rho_probe+C_probe)/R),
    S_compile=R ceil(C_compile/R),
    A_joint=S_init+m S_pair+S_compile.

Here m is a predeclared worst-case comparison bound for the chosen algorithm, including m_max for mission-aware acquisition, not its favorably observed stopping count.

Atomic batch construction, capacity, pre-tick submission and guards must be included in these bounds or separate reserved setup. Processing at an endpoint precedes the next admission; a physically necessary positive guard is not rounded away.

If work facts are not already acquired and paid, singleton P_i,D_i tests at J=0 measure Q,2Q on this fixture. Reserve their slots from the public caps before observations, not from the as-yet-unlearned realized durations. Add

    A_local=sum_i R ceil((D_P+rho_P+C_P)/R)
           +sum_i R ceil((D_D+rho_D+C_D)/R)
           + separately rounded local setup/validation.

This costs 2n local invocations and 2m joint invocations, none substituting for a fresh productive invocation. Fix grid-aligned commissioning deadline T0 independently and require A_local+A_joint<=T0, or explicitly declare A_local sunk. For K production bursts pay their actual final calendar time, interburst drain/idle, 2n+2m+Kn invocations when local learning is included, finite arithmetic, buffers, retained evidence, payload/permutation storage, energy, command/tail costs and retention leases. Exact rational timing requires bounded representations and charged arithmetic; integer Q fixtures require no real-number oracle.

Once total priority is known, report k belongs to pi_k, so each tight-deadline production succeeds under gamma. More generally the compiled uniform role-word criterion suffices without total identification. For fixed P where only payload-sensitive acceptance is promised, gamma must cover the actual per-burst checker and refusal is not completion.

Ordinary drained serialization remains legal if its deadline and unchanged retention capability permit it: release P_i at (i−1)R and complete by

    H_serial=(n−1)R+Q+gamma.

Pay stored earlier bits and all idle waiting. There is no one-shot end-to-end speedup claim: acquisition may dominate one mission; repeated use may amortize it.

### Restricted information lower bound

In a pair-comparison-only decision tree with no initial order evidence, each probe reveals one binary relation. Uniform arbitrary-payload correctness requires each terminal evidence class to have a single role word. With n_a modules of role a there are n!/(product_a n_a!) possible role words. Hence some branch requires at least

    ceil(log2(n!/(product_a n_a!)))

binary comparisons. For distinct roles this is ceil(log2(n!)); for a single role it is zero. This is only a decision-tree lower bound for these binary pair probes, not a claim about unrestricted multiway timing experiments, which may have many outcomes. Existing local evidence changes the relevant count of possible role words.

## 9. End-to-end scoped conclusion

Suppose local work/FIFO/callback contracts are sound, primitive arbitration and batch capabilities hold, joint evidence retains the actual persistent priority, every L_j>J, and all closed-horizon, physical-bridge, retention and finite resource conditions above hold. Then a passing exact poset certificate commands the actual role vector safely within its charged execution envelope. If compilation establishes the uniform role-word condition, every allowed productive payload/lag realization passes; if complete priority is acquired by the fixed-demand pair protocol, that condition is guaranteed. Fixed commissioning and mission deadlines must cover the explicit acquisition and production bounds; successful refusal is never substituted for useful completion.

The n-family shows why unchanged valid local intrinsic contracts and complete separate learning alone do not supply this conclusion. The safe joint protocol supplies the missing wiring evidence at finite cost. The four-job example shows why retaining that evidence as joint precedence, rather than marginal report windows, can strictly strengthen an efficiently checkable anonymous mission certificate.

No claim is made to discover arbitrary scheduler/resource semantics, prove work invariance from observations, remove physical bridge assumptions, analyze unbounded external traffic, obtain general polynomial exact scheduling, or establish novelty/optimality against all identification methods.
