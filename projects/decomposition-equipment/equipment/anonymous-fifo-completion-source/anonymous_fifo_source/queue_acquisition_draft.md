# Anonymous FIFO acquisition: scoped deterministic result

Status: conditional constructive result, not a novelty or whole-contract theorem. No tags, report channels, source echoes, or stable report ranks are assumed. No stochastic jitter assumption is used.

## Model promises (not learned by this construction)

There are n addressed operation types. Each repeat invocation of type i joins its fixed but unknown server, has fixed duration τ_i in (0,D], and produces exactly one reliable report on completion. Servers are work-conserving, nonpreemptive FIFO and execute independently. Report delivery lag is independently adversarial in [0,J]; no statistical independence is intended. Reports reveal only arrival time and arbitrary payload. Clock, release timing, D, J, address-to-operation behavior, repeatability, and service/payload independence are trusted. Multiple simultaneous submissions to one server have some fixed or arbitrary FIFO tie order; pair sum arguments do not depend on that order.

Safe repeat probes require an independent no-actuation/isolation gate that preserves the same queue membership and service law as production. Merely discarding reports is not adequate isolation if requests themselves actuate. Initial idle must be established by a trusted reset or a bound on every outstanding request; D alone does not bound an unknown backlog. Once idle, a solo is fully drained after D+J and a pair after 2D+J. The endpoints are included and all arrivals at the endpoint processed before another probe; implementation guards can be added and charged.

These are substantive remaining premises. The construction learns partition and service intervals, not FIFO, repeatability, the isolation gate, delay bounds, or reliability.

## Safe acquisition

From idle, invoke i alone at time zero and record its sole arrival a_i. Set L_i=max(0,a_i−J), U_i=min(D,a_i), interpreting a zero lower endpoint as open because τ_i>0. Then τ_i∈[L_i,U_i] and U_i−L_i≤J.

For each unordered pair i,j, first calculate

    S_ij=max(U_i,U_j)+J,
    C_ij=L_i+L_j.

If S_ij<C_ij, invoke both simultaneously from idle. Let m_ij be the maximum of their two anonymous arrival times. If separate servers, m_ij≤S_ij. If the same server, the last completion is τ_i+τ_j and therefore m_ij≥C_ij. A threshold strictly between S_ij and C_ij identifies same/different exactly. Neither arrival is assigned to a job during this test. Return the partition from the exact pair relation (and reject inconsistent observations/model violations).

If some pair lacks a gap, this sufficient algorithm may return inconclusive rather than invent a relation. If all τ_i>3J, every certificate passes under every allowed solo jitter realization: with U_i=max(U_i,U_j),

    C_ij−S_ij = L_j−(U_i−L_i)−J ≥ τ_j−3J > 0.

The correlation U_i−L_i≤J matters: treating the endpoints as independent gives an unnecessarily weak 4J bound. The 3J strict bound is worst-case sharp for this particular pre-certified band test, absent clipping: choose one solo delay J and the other's zero, with the maximal-U type selected appropriately. This is not an impossibility theorem for all acquisition algorithms.

A conservative wall-clock cost is

    A = n(D+J) + binom(n,2)(2D+J),

using n² individual invocations in total. Any reset, isolation, dispatch, endpoint guards, or validation cost must be added. Pair testing can be optimized using certified representatives, but all pairs already give finite exact recovery. There is no IID, confidence-level, or uncharged discovery assumption.

## Constructive post-acquisition production schedule

Suppose learned partition has q queues, each with at most h production jobs, one invocation of its addressed type. Let

    L=min_i L_i, U=max_i U_i, W=U−L.

These are a global enclosing interval, NOT an intersection. An intersection is unsound unless equality of durations is independently promised. The following check works for arbitrary fixed heterogeneous τ_i within their learned intervals.

Choose a positive margin η and Δ satisfying

    Δ > hW+J,
    L > (q−1)Δ+hW+J.                         (1)

This is an explicit numerical certificate from acquired data, not an oracle asserting that a good schedule exists. Queue r∈{0,…,q−1} receives its first actual production job at rΔ. Release all remaining jobs of that queue in a known strict FIFO order after rΔ but before rΔ+L; e.g. offsets (k−1)ε with (h−1)ε<L. Hence no server idle gap occurs after its first start. Real implementation dispatch constraints must permit these releases and be charged if relevant.

The k-th completion in queue r belongs to

    [rΔ+kL, rΔ+kU],

and its report arrives within

    I_rk=[rΔ+kL, rΔ+kU+J].

Within a stage k, adjacent queue windows are disjoint because Δ>kW+J. Between the last queue at stage k and the first queue at stage k+1, disjointness follows from L>(q−1)Δ+kW+J. Condition (1) conservatively covers every stage, including absent jobs in shorter queues. Therefore timestamp alone assigns every report to its production job. This rank behavior is a proved consequence of this chosen schedule, not a supplied report-order assumption. General schedules may instead retain multiple compatible associations in a joint matcher.

The schedule drains by

    T=(q−1)Δ+hU+J,

while actual work on an equal-duration balanced fixture ends at (q−1)Δ+hτ. The first release in every queue is a real production job, not a free queue-start marker.

## A growing positive fixture without a homogeneity promise

Let n=qh, q≥2, and take a world in the broad heterogeneous model whose actual durations happen all to equal τ. Acquisition still uses individual intervals: for arbitrary solo jitters, L≥τ−J, U≤τ+J, and W≤2J. Taking Δ=(2h+1)J+η makes the first part of (1) hold. A sufficient truth-level condition guaranteeing its second part for every solo jitter is

    τ > q(2h+1)J + (q−1)η + J.

Also require τ≤D and the acquisition margin τ>3J. These conditions show a nonempty scalable favorable subfamily when the known service bound permits it; the algorithm itself checks (1) from data and does not assume or infer exact equality. Constants can be improved using per-queue cumulative intervals rather than the global envelope.

## Budget caveat: acquisition cannot be silently amortized

For a single real n-job batch, an end-to-end speedup over serial nτ is impossible for this particular acquisition protocol on an equal-duration fixture: its n isolated solo probes alone take at least nτ, before any pairs or real work. A large enough B gives feasibility A+T≤B, but that fact is NOT a one-batch speedup theorem.

For K repeat production batches on the same stable system, separated by drains, the explicit total upper budget is

    B_required=A+K T.

Serial execution of the same K production batches needs at least K nL service time. Thus a sufficient, fully charged speedup certificate is

    G=nL−T>0, and K>A/G.

Choose an integer K strictly above A/G, and a budget B≥A+KT. For sufficiently large τ/J and balanced q≥2, G>0. This is an amortized theorem with stable repeatable production batches; repetitions are an added task condition, not permission to change a single-batch benchmark. Alternatively report acquisition cost and post-acquisition speed separately without claiming end-to-end gain.

## Scope boundary

Recovered membership and certified timing association do not certify arbitrary payload meanings or downstream control safety. Unknown start/end packet fields are not reconstructed: the model supplies one completion report per job, and FIFO plus windows establish its origin. Compare against existing finite-model discovery, unlabeled inverse problems, callback learning, and prior tagged queue-group learning before asserting novelty.

An alternative task contract is a separately paid commissioning phase followed by an exogenous mission-release time and mission latency deadline. Then A is charged to commissioning and T is checked against the real mission deadline; no total speedup is asserted. This phase split must be stated by the problem, not retroactively chosen to make a benchmark pass.

A baseline still requiring comparison is global job staggering after solo duration acquisition, without partition learning. In favorable near-homogeneous worlds this can sometimes enforce anonymous timing separation with roughly n offsets rather than q offsets. Therefore the favorable fixture above does not by itself prove partition learning necessary for safe concurrency or any all-policy impossibility result. The narrower achieved claim is a concrete finite safe partition-acquisition procedure and a useful certified schedule from its output.
