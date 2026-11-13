# Established baselines and scope

31 October 2026. Scope: shared-resource transport of learned local FIFO and anonymous-callback certificates. This is a bounded primary-source comparison, not an exhaustive survey or a novelty conclusion.

## Result first

**Unknown arbitration is already covered by a directly applicable classical theorem.** The possible residual target is not merely turning isolated service costs into shared delay bounds. It is establishing sufficient joint evidence for an anonymous productive job/report assignment certificate, while charging the evidence acquisition, schedule, checking, and physical tail. Whether that combination has prior art remains unestablished by this bounded comparison.

## Verified network-calculus baseline

Primary source: Jean-Yves Le Boudec and Patrick Thiran, *Network Calculus*, online version August 23, 2022, [author-hosted PDF](https://leboudec.github.io/netcal/latex/netCalBook.pdf).

- Theorem 6.2.1, printed p.176 (PDF p.194): with **unknown arbitration**, strict aggregate service curve β and cross-flow arrival curve α₂ imply flow-1 service curve β₁(t)=[β(t)−α₂(t)]⁺, provided β₁ is nondecreasing.
- For β(t)=Ct and α₂(t)=b+rt, C>r, leftover service has rate C−r and latency b/(C−r).
- Printed p.177 explicitly gives a counterexample when aggregate service is not strict; FIFO can support another result, Proposition 6.2.1, under its stated assumptions.
- Theorem 1.4.2, printed p.23: arrival curve α and service curve β bound **virtual** delay by horizontal deviation h(α,β).
- Theorem 1.4.6, printed p.28: consecutive systems offering per-flow curves β₁,β₂ offer β₁⊗β₂ jointly. Rate-latency concatenation takes minimum rate and sums latencies.

These are existing theorems, not results to repackage as novel transport.

## Verified hierarchical-contract baseline

Primary source: John Regehr, dissertation, [Chapter 5, Composing Scheduling Policies](https://users.cs.utah.edu/~regehr/papers/diss/doc-wwwch5.html).

Sections 5.1–5.3 represent a scheduler by the guarantees it requires and provides, with conversion through scheduler implementations or rewrite rules. Basic reservations promise allocation within scheduler-chosen periods; continuous reservations promise it in every interval of the stated length. These are not interchangeable guarantees. The conversion table treats the required input guarantee as a precondition, and resource amounts under a uniformly slower processor use that processor's time domain. Section 5.3.1.1 notes that preemptive fixed priority transfers its input guarantee to the highest-priority child but gives lower children no guarantee: the highest child can be CPU-bound. Section 5.3.1.2 warns that independently supplied guarantees cannot simply be added on multiprocessors when service overlaps and a child cannot consume both.

This is a close prior framework for conditional local-to-shared resource guarantees, not an anonymous-report binding result.

## Implications for the shared resource model

The following is our analysis of the supplied theorem, not a claim made in either source.

1. **Separate demand from delivered service.** A local measured duration can represent intrinsic resource demand only if wiring preserves that demand law. Its isolated wall-clock recurrence C_k=max(r_k,C_(k−1))+τ_k generally does not survive suspension/contention. In shared mode, establish a delivered-service contract and the exact completion semantics before transporting windows.
2. **Do not smuggle in a reservation.** Learning τ_i or the isolated FIFO partition does not establish strict aggregate service, cross-traffic admission limits, maximum interruption, initial backlog, or a reservation. These must be trusted, enforced, or justified by the new evidence. Finite favorable samples alone do not certify arbitrary future adversarial scheduling.
3. **Unknown scheduling is compatible with known coarse bounds.** If the blind-multiplexing hypotheses are already supplied, derive a conservative shared completion envelope from them. Do not characterize all unknown schedulers as a no-bound case. Conversely, arbitrary uncontrolled interference may invalidate finite bounds.
4. **Virtual delay is not automatically a named-job deadline.** Preserve per-queue FIFO/order, or prove a different bridge from cumulative delivered work to each invocation's completion. Packetization, nonpreemption/blocking, time units, and callback delay need explicit interpretation.
5. **Timing and assignment are different layers.** With valid shared completion windows and a closed reliable one-report-per-job horizon, the existing global perfect-matching coverage argument still applies. Then universal role-vector agreement is a sound certificate. Service curves alone neither expose callback origins nor prove parity invariance.
6. **Widening can destroy acceptance without destroying soundness.** More conservative shared windows add possible matching edges. Re-running the checker remains sound if actual matching coverage holds, but may produce UNRESOLVED. Old isolated edges cannot be retained merely because they were once valid. Two differing graph matchings do not prove two physically realizable worlds.
7. **Timing-preserving reports are not sufficient for physical transport.** Preserve payload-to-role/load relation, fresh productive jobs, retention leases, output latency, safety gate, and final tails separately. Resource guarantees do not imply these.

## Appropriate comparison claim

“Classical network calculus and hierarchical scheduler contracts supply conditional resource-service composition. This work investigates what additional joint evidence suffices to transport a particular learned FIFO timing certificate into a shared context and to certify task-relevant values from anonymous reports, including cost and failure/refusal accounting.”

This is a scope description, **not** a novelty conclusion.

## Deliberately bounded exclusions

No theorem-level claim about observational/contextual equivalence was necessary for the closest baseline. Local observational equivalence need not survive a shared context, but presenting that general slogan adds less than explicitly specifying the admitted contexts and proving coverage. No formal contextual-equivalence source was reviewed, and no claim that our preservation condition is new or complete is made. A future novelty survey would need anonymous sensing/data association and assume-guarantee/contract literature in addition to these resource-service baselines.

## Poset parity certificate baselines

### Directly verified standard ingredient

Colin Defant and Noah Kravitz, *Friends and strangers walking on graphs*, Combinatorial Theory 1 (2021), #6, **Proposition 1.3, printed p.4**, states connectivity of the linear-extension family under toggles that swap adjacent incomparable elements. The immediately following discussion explicitly identifies the standard use of this fact: proving that a construction is independent of the chosen linear extension. Thus both the connectivity ingredient and the general local-swap-to-global-invariance proof pattern are established, not new. [Primary journal PDF](https://escholarship.org/content/qt7299j21s/qt7299j21s.pdf).

The older primary literature studies considerably stronger enumeration questions. Frank Ruskey, *Generating Linear Extensions of Posets by Transpositions*, JCT B 54 (1992), 77–101, concerns listings by single transpositions and conditions for special posets. Its author-hosted abstract does **not** itself establish the precise adjacent-rank interval lemma in Section 4 of transport_theorem.md. [Author page](https://webhome.cs.uvic.ca/~ruskey/Publications/JCTextension/JCTextension.html). Gara Pruesse and Frank Ruskey, *Generating Linear Extensions Fast*, SIAM J. Comput. 23(2) (1994), 373–386, gives constant-amortized-time generation, including a listing where consecutive outputs differ by one or two adjacent transpositions. [Primary publisher abstract](https://epubs.siam.org/doi/abs/10.1137/S0097539791202647). Do not confuse connectedness with existence of a Hamilton path using exactly one adjacent swap at every step.

### The role parity specialization

For fixed observed bits b and role labels rho, our vector statistic is F(sigma)=sum_k b_k e_rho(sigma_k) over F₂. The change on one allowed adjacent swap of x,y at positions k,k+1 is (b_k+b_(k+1))(e_rho(x)+e_rho(y)). Connectivity therefore reduces global constancy exactly to vanishing on every allowed swap. This is a direct specialization of the standard invariance method, not an independent foundational theorem.

The additional operationally useful compression is the explicit support of the possible swap positions for each incomparable pair:

    |Pred(x) union Pred(y)|+1 <= k <= n−|Succ(x) union Succ(y)|−1.

Section 4 of transport_theorem.md proves the interval using nested downsets; together with bit-transition prefix sums it avoids enumeration and yields the stated polynomial test. The bounded searches for adjacent-incomparable connectivity, positional invariance, and predecessor/successor rank constraints did not establish a prior source for this exact compressed role-parity criterion. **This is an unresolved attribution question, not evidence that the criterion is novel.** Cite the standard connectivity result and present the interval and specialization with their own elementary proofs.

The four-job example establishes a concrete strict gain over the existing marginal-rank matching relaxation. That comparison is internal and mathematical: enforcing all precedence correlations can certify this record where independent marginal compatibility cannot. It does not demonstrate a separation from all known poset algorithms or all previous anonymous-association methods.

### A different parity statistic

Sign-balanced-poset work studies counts of even and odd permutation signs among linear extensions. Dennis E. White's *Sign-Balanced Posets* explicitly concerns such sign balance and imbalance for poset classes. [Primary publisher abstract](https://www.sciencedirect.com/science/article/pii/S0097316500931467). That is a different statistic from XOR of an arbitrary fixed rank-bit word grouped by job roles; it is neither a verified solution nor a verified obstruction to our problem. Chan–Pak's [survey](https://www.math.ucla.edu/~pak/papers/LEsurvey11.pdf) was used only as a locator, not as original-theorem evidence.

**Attribution summary:** “Using the standard connectivity of linear extensions under adjacent incomparable swaps, we derive a fixed-payload role-parity test by characterizing the feasible adjacent positions of each incomparable pair. The result is exact for the declared poset abstraction; its physical completeness and literature priority require separate claims.”
