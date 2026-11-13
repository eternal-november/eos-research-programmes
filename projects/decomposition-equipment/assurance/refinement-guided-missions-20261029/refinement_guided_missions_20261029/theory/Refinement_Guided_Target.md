# Refinement guided discovery of delayed resource interfaces

29 October 2026. Prospective target and derivation. No experiment has been run for this target.

## Decision

The strongest feasible target is not another Boolean-door mission. It is safe, task-directed discovery of unknown delayed shared-resource interfaces, followed by reuse for genuinely new overlapping service workloads. Thermal/actuation load is a useful physical interpretation, but a finite impulse response must be declared as a synthetic class or accompanied by a justified truncation tail. It is not automatically an exact thermal RC model.

The contribution sought is the connection between safe evidence acquisition, discovered temporal interfaces, and reusable certification. Coded identification, robust optimization, CEGAR, sparse convolution, and scheduling are established mechanisms. This proposal does not claim a new basic mechanism or literature priority.

There are two different evaluations:

1. A prospective strictness theorem demonstrates that the mission actually needs the distinctions erased by a stated coarse interface. This is a model/certificate separation, not proof that every controller with the original raw records is physically incapable.
2. An information-equivalent dense temporal model and a known-structure oracle are serious baselines. They should match the learned model's attainable capability. The potential benefit of decomposition is reduced acquisition, representation, certification, or reuse cost; a capability win over them is neither expected nor required.

## General mathematical setting

Let u(t) be a vector of bounded nonnegative commands. A resource readout has the form

    y_i(t) = sum over j and l of G[i,j,l] u_j(t-l) + e_i(t).

The lag ceiling L, coefficient bounds, measurement/error envelope and command alphabet are supplied. Actual nonzero scopes, lags, weights and useful local observers are unknown. Persistent G is selected once, not resampled at each command. Bounded errors and an unmodeled tail, if used, belong to the robust physical contract and remain charged throughout.

Mission state consists of useful work completed, precedence/release conditions, elapsed time, power/energy budget and a physically justified startup state. Positive service demand excludes all-off as success. The capacity conditions y_i(t) <= c_i must hold during every segment and after the final command until the complete lag/stopping tail clears. A controller may use only its declared observations and history.

The smallest rigorous discovery subclass has one unknown current input and one unknown delayed input per resource:

    y_e(t) = u_{a_e}(t) + u_{b_e}(t-d_e),
    a_e != b_e, 1 <= d_e <= L.

No actual endpoint pair, role assignment or delay is supplied. This two-tap class is a starting theorem, not the full motivating benchmark. The larger family should include overlapping multi-tap resources, heterogeneous weights, pulse durations, precedence/release windows, and multiple mission compositions, while retaining a checkable robust residual envelope.

## Law 1 -- epistemic refinement preserves guarantees

Fix the same controller class, observation interface, physical starting state, tasks, actions and resource accounting. Let K_f be a coherent persistent-model set and let K_c contain it. A policy winning for every G in K_c also wins for every G in K_f. Therefore the robust winning-policy sets are nested and the optimal worst-case completion cost cannot increase when K_c is replaced by K_f.

This proof is universal restriction, including all permitted adaptive observation branches. It neither gives extra sensor access nor allows a policy to depend on the hidden G. It does not establish strictness.

If the change is merely a different factorization of the SAME coherent K, the winning policies are unchanged. Only computation/representation cost can improve. This distinction must remain visible in all comparisons.

## Law 2 -- a prospective temporal strictness witness

This seed is a sanity witness, not sufficient by itself as the main research result.

Take n=2q positive jobs. Each job must receive one unit service pulse in slots 0 or 1. Shared power permits at most q pulses per slot. Resources form a connected path on the jobs. For each edge there is one current endpoint and one one-slot-delayed endpoint; its capacity is one. A fine interface knows the ordered roles. The coarse interface retains the unordered pair and the fact that exactly one endpoint is current, but forgets which endpoint has which role. It therefore includes both fixed orientations of each resource. A coarse controller can plan intelligently, retain its entire permitted summary history, and observe delivered runtime resource measurements.

Choose a fine directed path orientation with a topological order. Serve the first q vertices in this order in slot 0 and the rest in slot 1. For an edge within a batch, its two contributions occur one slot apart. For an edge crossing batches, the current endpoint is in the earlier batch and the delayed endpoint in the later batch, so the contributions again never coincide. Every resource stays at most one, including slot 2's terminal tail. All jobs finish their commanded service by slot 1.

Now consider ANY coarse robust policy that guarantees the same workload by slot 1. The power limit forces exactly q jobs in each slot. Its initial slot-0 batch is fixed by its currently permitted history (and seed). Since the path is connected and both batches are nonempty, some resource edge crosses the cut. The coarse set contains a PERSISTENT orientation with the first-batch endpoint delayed and the second-batch endpoint current. In that environment both contributions occur in slot 1. A runtime observation can reveal the problem but cannot make the remaining q jobs complete by the deadline without using that unsafe second pulse. Thus the policy must violate capacity or miss the goal. This is a strict robust certificate gap, not just a particular coarse planner's failure.

The quantifier is 'for every policy there exists a coarse-compatible fixed environment'. It does not require one orientation to spoil every possible policy. Randomization does not produce a probability-one robust completion guarantee under this zero-risk obligation. For every realized controller seed, its nonempty cut has a violating orientation. There are finitely many orientations. If each fixed orientation had failure probability zero, the finite union of those seed-failure sets would also have probability zero, contradicting that it covers every seed. Thus some fixed orientation has positive failure probability. The argument does not let an adversary observe the private seed before choosing the environment.

This theorem does NOT apply to a nominally coarse controller that secretly retains the raw commissioning trace and reconstructs the ordered roles. The coarse observation/summary interface must be stated exactly. Nor may it discard constraints its stated interface actually preserves. The fine/coarse separation is a mission relevance sanity check, not the competitive algorithm comparison.

## Law 3 -- causal safe discovery of the two-tap interfaces

Assume a justified startup envelope and execute a charged all-off flush sufficient to clear L ticks of pending input. Use a public binary code with distinct nonzero codewords for n command ports. For each code bit, issue one pulse of amplitude epsilon on precisely those ports whose bit is one, then hold all commands off through the complete L-tick tail. Record every permitted resource output at each tick.

Choose epsilon so that both (i) 2 epsilon plus the error/tail allowance is at most each resource capacity, and (ii) the maximum simultaneously active codeword population times epsilon respects shared power. Thus the acquisition is safe uniformly over every initial two-tap mechanism, not because the true support is already known. Any physical cooldown/setup time and every readout bit are charged.

At pulse time the readout is epsilon times the code bit of a_e. At delay d_e it is epsilon times the code bit of b_e. Across code tests the nonzero current signature identifies a_e, the delayed signature identifies b_e, and the nonzero delayed timestamps identify d_e. Zero codewords are prohibited so a port cannot disappear from every delayed measurement. If noise is present, require a signal gap allowing unambiguous zero-versus-epsilon classification; an epsilon that shrinks below the supplied sensor resolution is not allowed. If the power/sensor constraints make the code infeasible, use bounded-size command groups and count the additional probes, or report unavailable acquisition.

The procedure uses O(log n) isolated coded pulses and O((L+1) log n) causal time for the noiseless parallel-readout class, plus startup and explicit physical overhead. It avoids enumerating the joint hypothesis set. This is standard coded system identification specialized to the permitted interface; it is not claimed as a new discovery algorithm by itself.

For general nonnegative s-sparse multi-tap rows, a disjunct/group-testing design with a known minimum nonzero coefficient and adequate noise gap is a possible extension. Its support, coefficient and absence-certification arguments need to be written and checked before claiming the corresponding sample bound. Arbitrary analog input amplitudes can encode more information than binary pulses, so no universal optimal sample lower bound is asserted here.

## The central algorithm -- evidence constrained refinement

The intended procedure must not identify everything and then merely call a scheduler.

1. A generator proposes a local interface representation and a mission controller/certificate using current evidence.
2. A trusted checker verifies full-tail capacity, resources, progress and observation permissions against ONE coherent persistent model set. If successful, preserve the certificate for reuse.
3. If a coarse abstraction produces a spoiling strategy, check its consistency with the exact retained evidence. An incoherent obstruction can be eliminated by a logically justified interface/refinement step without taking new physical measurements.
4. If the obstruction is consistent, find a permitted safe diagnostic that separates the relevant local operator alternatives, execute it only from its verified physical precondition, charge its cost, and branch on every possible result. A result may certify progress, require further refinement, or justify safe abstention.
5. Reuse only interfaces and module certificates whose input/history/resource assumptions still apply. New task compositions must not be silently treated as new physical input regimes.

This differs from known-model CEGAR only in the substantive burden of safely obtaining evidence for a refinement. A finite-model exact belief game remains a reference definition, not an efficient algorithm hidden under the word 'oracle'. Generic global synthesis can be exponential. A useful theorem needs an output-sensitive bound in local catalogue size, acquired separator/query width, selected probes and checked policy graph, not a claim that sparsity alone makes planning easy.

Coherence has a quantifier subtlety: to refute existence of a robust policy, different proposed policies may be defeated by different fixed models. A counterstrategy is not invalid merely because counterfactual CONTROL branches use different models. Along each actual observation history the retained model explanation must remain possible, and across environment branches the game semantics must preserve the appropriate initial hidden choice. The checker must not demand a single model defeating all policies simultaneously, nor allow a model to switch conveniently during one realized execution.

## Direct rehearsal is a mandatory baseline

For a truly linear model with adequate sensing, a scaled low-amplitude replay of a candidate service schedule may certify the corresponding full-amplitude trajectory without discovering an operator. This is a strong shortcut, not an unfair baseline to exclude. Therefore one successful mission is insufficient evidence for the value of decomposition.

The intended payoff is cumulative cost across genuinely new task compositions: a learned local temporal interface can certify new schedules without physically replaying every schedule. Compare total safe acquisition time, sensing/communication, commissioning delay, planning/checking work and reuse cost against (a) direct scaled rehearsal, (b) an optimized information-equivalent dense persistent temporal model, and (c) a known-interface oracle. Report crossover points and cases where direct rehearsal is better. The dense model may exploit zeros or recover the same sparse factorization; that is legitimate and must not be prohibited to manufacture a win.

## Release gate before experiments

- Prove the fine strictness schedule and coarse all-policy obstruction before selecting outcome seeds.
- Name the exact coarse summary/interface and ensure its retained evidence is respected.
- Keep the path seed only as a regression/sanity witness. The main workload must have overlapping multi-lag, multi-stage jobs, nonzero sustained activity, varied compositions and terminal-tail accounting.
- Demonstrate discovery of actual unknown scopes/roles/lags, not merely selection among supplied whole models.
- Give a checked safe probing protocol with startup, amplitude, noise, sensing, shared-power and cooldown costs.
- Expose generic synthesis cost and actual query width.
- Keep dense coherent and direct rehearsal baselines. Matching their capability is expected; claim only verified cost or reuse differences.
- Do not run the proposed main experiment until independent target review approves these conditions.

## Current status

The refinement law, the two-slot temporal separation seed and the coded two-tap acquisition argument are derived above. The appended sections now provide a concrete multi-tap class, a verified-code acquisition proposition, and a reliable column-directed finite-progress algorithm. Independent target review has passed these as a restricted but substantive integration direction. Numerical mission parameters and outcomes still require a separately frozen protocol and execution. The simple path seed remains a relevance witness, not completion of the hard research target.

## Concrete extension and acquisition theorem

The following multi-tap acquisition proposition supplies a reliable implementation target without assuming an unproved compressed-sensing oracle.

For every resource row i, at most s pairs (j,l) have a positive coefficient. The coefficients lie in a supplied finite grid {0, Delta, 2 Delta, ..., g_max}. The actual nonzero pairs and values are unknown. Lags lie in {0,...,L}. The physical model is exactly this finite FIR for the synthetic theorem. A separately certified tail/noise extension may use the same argument only after adding its error to the bounds below.

Let A be an R-by-n binary test matrix that has been VERIFIED to be s-disjunct: for every input j and every set S of at most s other inputs, some test row has A[r,j]=1 and A[r,k]=0 for every k in S. Use its actual R and maximum row population w_max; do not substitute an unverified asymptotic claim. A singleton identity matrix is always a fallback, with R=n and w_max=1. Code construction and disjunctness verification costs are separate and explicit.

Run one isolated input pulse epsilon A[r,:] for each requested test row, followed by L all-off ticks. Read every permitted output over lags 0 through L. At a fixed output i and lag l the measured response is

    z[i,l,r] = epsilon sum_j G[i,j,l] A[r,j] + noise,
    absolute noise <= eta.

Assume epsilon Delta > 2 eta. Choose a threshold strictly between eta and epsilon Delta - eta. A true nonzero coefficient at (i,j,l) makes every test including j exceed that threshold. If that coefficient is zero, s-disjunctness gives a test containing j but none of the at-most-s positive inputs at this lag, and that test remains below the threshold. Thus a coefficient is nonzero EXACTLY when no test containing its input gives a below-threshold measurement. This recovers each lag's support without listing complete environments.

After support recovery, choose for every supported j an isolating test containing j and no other supported input at that lag. Such a test exists by disjunctness. Its measured value divided by epsilon is within eta/epsilon of the coefficient. Since eta/epsilon < Delta/2, rounding to the supplied grid recovers the coefficient exactly. Multiple supported taps on one input at different lags are handled at their separately observed timestamps. No claim about continuous arbitrary coefficients follows from this finite-grid argument.

The entire probe is uniformly safe when

    epsilon s g_max + physical residual allowance <= c_min,
    epsilon w_max <= shared power limit,
    0 < epsilon <= command amplitude limit.

Each isolated pulse has no overlap with the preceding pulse's tail. A verified startup/flush envelope handles any pending initial input. If these upper bounds leave no epsilon satisfying the sensor-gap lower bound, this code is infeasible; the program must use a different admissible code/amplitude, spend more acquisition time, or abstain. Shrinking epsilon as n grows is NOT free when sensor resolution is fixed. Singleton tests improve the power and peak-response bound, and may be the best actual acquisition method.

The full protocol costs at most R(L+1) command ticks plus startup and physical sensing/cooldown overhead, and m R(L+1) output samples if all rows and lags are read. Data processing for elementary support filtering costs O(m L R n), with the actual output count and storage charged. Sparse support helps the resulting representation and future convolution checks, but singleton acquisition alone does not become cheaper merely because the true operator is sparse. A dense matched-class learner receives the same sparsity/grid promise and the same records.

## Finite task directed acquisition guarantee

The verified code can be used as a finite library rather than executed blindly. Maintain the exact persistent coefficient set K_D consistent with issued tests and the structural class. For a proposed mission policy, the checker may return a compatible violating operator or a failed interface obligation. A policy rejection is not proof of physical impossibility.

When two retained operators disagree on a mission-relevant response, their complete noiseless code signatures differ in at least one test, because the preceding reconstruction theorem makes the complete code injective on the class. Under the grid/error condition there is a separating code measurement. Select an as-yet unissued relevant test, execute it through its safe protocol, and retain every operator consistent with the bounded measurement. Never eliminate the true operator by assuming the desired outcome. Every issued test is charged and no test need be repeated for the finite exact-grid guarantee.

After at most R distinct tests, the true operator is identified within the declared class. At that point an exact complete synthesizer for a DECLARED finite mission grammar either returns a verified feasible policy or correctly reports no policy in that grammar using the remaining resources. Before full identification, it may return a policy robust over K_D, allowing early accepted completion and partial identification. This is not a polynomial-time planner claim; controller synthesis and local-consistency queries can be expensive and their actual costs remain visible.

This termination statement is conditional on a safe acquisition reserve and on enough remaining task time/resources. It does not guarantee that every true operator admits the requested mission. A uniform initial completion theorem would additionally require viability for every possible operator after the worst-case acquisition cost, or a smaller verified branching acquisition policy whose leaves are all winning. Accepted branches complete; other branches safely abstain. The algorithm may fail to achieve a useful mission even while every probe is safe.

## Fixed substantive mission family for the next gate

A suitable main family uses n in a growing set, s between two and four nonzero taps per resource, multiple lags, finite positive coefficients, and several resources sharing command ports. A mission contains multiple positive-service jobs, each with two or more ordered stages, stage durations, release/deadline windows, and alternative permitted command sets where physically meaningful. Shared power and complete delayed capacity tails constrain interleaving. Every successful policy must perform nonzero useful commands; merely waiting, stopping, or observing cannot satisfy a job. New missions change stage combinations, overlap and release patterns, not only the order of identical independent passages.

Low-amplitude probes must not have their useful service silently discarded. If the job model credits fractional service, credit it equally to every method. Alternatively commissioning can occur at a calibration station before job release, or service can require a declared indivisible actuation/stroke that a subthreshold diagnostic does not accomplish. That is a task/physical premise, not a convenient scoring rule added after outcomes.

The temporal path theorem compares already-acquired fine and coarse interfaces at the same physical starting state. End-to-end results additionally pay each method's actual commissioning, pending tails and setup/transfer time before the mission deadline. A strict post-commissioning separation alone is not an end-to-end performance win.

The code-based and singleton acquisition methods, direct scaled mission rehearsal, coherent dense operator method and known-operator oracle all remain eligible. The first experimental question is not 'does the chosen method win every comparison?' It is whether certified mission relevance survives full accounting, and at what number and diversity of new tasks the reusable discovered interface repays its acquisition and checking cost.

For a fixed set of Q new mission schedules with horizons T_k, let D be total safe discovery time and overhead. A declared non-reusing direct-rehearsal strategy pays sum_k(T_k+L+overhead_k) in extra physical commissioning before common service execution, while the reused operator pays D plus any new-interface acquisition. Comparing these measured quantities gives an amortization crossover. It is NOT a lower bound for every information-equivalent baseline: a clever rehearsal method may reuse its records to identify the same operator and must be allowed to do so. Optimized dense/cache methods can tie, and that outcome must be reported.

## Reliable first algorithm -- column directed safe refinement

The first implementation should use singleton-column probes. They give a clean finite refinement theorem without making coded-acquisition efficiency necessary for success.

### Exact safe singleton probe

After a justified full-lag flush, command input j at amplitude epsilon for one tick and then command zero for L ticks. At output i and lag l, the true response is epsilon G[i,j,l]. If measurement error is bounded by eta and epsilon Delta > 2 eta, rounding the measured value divided by epsilon to the coefficient grid identifies every coefficient in column j exactly. Its uniformly safe peak bound is epsilon g_max plus any physical residual allowance, NOT epsilon s g_max: one isolated input pulse contributes at most one coefficient at a given output and timestamp. Shared power is epsilon. The full input and tail cost L+1 ticks plus stated physical/readout overhead. The preceding command history must be flushed safely, not overwritten in memory.

### Exact robust fixed-schedule envelope

Let J be the already measured columns. In row i, let k_i equal s minus the number of known nonzero taps in those columns. Every unmeasured column remains unconstrained apart from the same nonnegative coefficient grid and the row's remaining sparsity capacity. For a proposed nonnegative schedule u, define Z_i(t) as the multiset of u_j(t-l) over all unknown-column pairs (j,l). The exact worst compatible resource value is

    known_convolution_i(t)
      + g_max * sum of the k_i largest elements of Z_i(t),

with missing elements padded by zero. Known zero taps cannot be chosen. The upper bound is attained by assigning g_max to the selected unknown taps and zero to the others, so the checker can return a PERSISTENT compatible row/operator witnessing a failed time inequality. The choice of worst operator may differ between distinct rejected schedules or times; universal schedule safety is forall G forall t, so checking every time's maximum is sound. This does not authorize switching G midway through an actual execution.

This formula relies on precisely the stated product-of-rows sparse-grid class. Additional row-sum, cross-row or coefficient relations must be retained and change the optimization. It cannot be used after silently forgetting known constraints. For a more informative acquired relation, a sound exact local optimization or explicit conservative overapproximation replaces the top-k formula.

### Finite progress proposition

Maintain the exact known columns and current physical/task/resource state. Solve a candidate scheduling problem using all known coefficients and setting unknown coefficients to zero. This is an optimistic relaxation because the model is nonnegative. Use a declared finite scheduling grammar and include the remaining original deadline, resources, and complete terminal lag tail.

- If the exact optimistic solver proves infeasibility, no real operator in the current class admits a schedule in that grammar from this state, since real coefficients only add nonnegative load. A heuristic timeout is not this proof.
- If it returns a schedule, apply the exact robust envelope above. On success the schedule is valid for every retained operator and may be executed.
- On failure, the violating inequality must contain a positively activated unknown tap: the optimistic candidate already respected the known convolution. Select an unmeasured input column from a witnessing positive contribution, execute its safe singleton probe, charge its elapsed time/resources, and repeat.

Every failed check resolves a previously unmeasured column. Therefore at most n such probe steps occur. At full identification the optimistic and actual model coincide, so a complete finite solver either returns a certified schedule or correctly rejects the remaining finite scheduling problem. Intermediate accepted schedules may leave irrelevant columns unidentified, and their learned interfaces remain available to later tasks.

The guarantee is safe finite diagnosis with conditional completion, not guaranteed useful success for every operator or deadline. Probe time may consume the opportunity to complete; the actual residual budget must be recomputed after every probe. The algorithm is also not claimed to be optimal in the number of probes: a better query can separate several offending columns, and an alternative route may avoid probing entirely. A common solver/candidate grammar must be used for matched baseline comparisons.

This is a concrete evidence-constrained CEGIS specialization: a proposed schedule is challenged by a compatible physical operator, and a safe experiment resolves part of that counterexample. It does not yet synthesize general observation-dependent mission policies. Its explicit finite progress depends on nonnegativity, column-identifying safe probes, the coefficient grid/error gap, a finite lag bound, exact robust checking, and a complete finite scheduling solver where an infeasibility conclusion is claimed.

The proposition supplies the initial integration-level research plan. General adaptive policy synthesis, optimal safe experimental design, unknown signed/nonlinear dynamics, and arbitrary persistent stochasticity remain outside it. Main experiments must still satisfy the multi-stage/reuse gate rather than substitute the simple temporal path seed.

## Author finite checks

`check_refinement_laws.py` checks the propositions using its own small exhaustive models, independently of the planned mission implementation. It verifies all eight orientations and six balanced first batches of a four-job path, 728 small rational randomized mixtures, 38,400 exact top-k equalities across 73 sparse coefficient rows and 200 knowledge states, 2,005 positive-unknown-tap counterexample steps, 15 bounded-noise coefficient-rounding cases, and the ambiguity at equality in the signal-gap condition. A finite-progress fixture covers all 73 true rows, with 63 accepted continuations and ten safe budget-limited abstentions, and never exceeds three probes for three inputs. Those fixture outcomes are theorem consistency tests, not a mission benchmark or an acquisition-optimality claim. Results and the checker source hash are in `refinement_law_checks.json`.
