# Payload-sensitive joint-binding certificate (2026-10-31)

## Scope and epistemic boundary

This is a polynomial, exact test of parity invariance **over all perfect matchings of a supplied compatibility graph**. It is a sufficient certificate for the actual mission only when the physical assignment is included in that graph. It neither learns the queue partition nor proves the timing-window coverage premise. It makes no automatic original-C5 or novelty claim: matching symmetric differences, alternating cycles, strongly connected components, and graph potentials are standard machinery; the construction below is proved directly.

Given n known jobs, exactly n received reports, one reliable report per job, a closed observation horizon with no unexplained carry-in/carry-out traffic, and valid timing bounds, a certified learned queue partition and parameter uncertainty set may predict conservative job delivery windows W_i. From **raw report timestamps** t_v and bits b_v, construct E = {(i,v): t_v in W_i}. A report index is an arbitrary row identifier, not an authorized source tag, FIFO rank, timestamp rank, or hidden observation. Tied timestamps are permitted. The job role c_i is known from the job specification, not inferred from the packet.

The required physical premise is one single global bijection M_actual whose every pair belongs to E. Correlated unknown delays, shared parameters, queue membership, and FIFO constraints can make many graph perfect matchings physically unrealizable. Do not replace this premise by independent favorable explanations per report; do not claim the graph is an exact joint physical model. If timing intervals exclude truth, this checker cannot repair that error. Noise/probabilistic coverage requires an explicitly stated coverage guarantee, not deterministic certainty.

For role r define output y_r(M) = XOR of b_{M(i)} over all jobs with c_i=r. A certified constant vector is the actual role-parity vector under the coverage premise. It need not equal a desired target: if the mission specifies y*, compare the certified vector with y*. Constancy alone establishes binding, not arbitrary semantic success.

## The theorem

Assume E has a perfect matching M0, written m(i). Construct a directed graph D on jobs with arc i -> j exactly when report m(i) is compatible with job j. Thus every vertex has its zero-weight self-loop. Let e_r be the r-th basis vector in F_2^g and assign

    w(i,j) = b_{m(i)} (e_{c_i} + e_{c_j}).

The following are equivalent:

1. y(M) = y(M0) for every graph perfect matching M.
2. Every directed simple cycle in D has XOR weight zero.
3. For each strongly connected component S of D there are potentials p_i in F_2^g such that w(i,j) = p_i + p_j for every arc with i,j in S.

Edges between different SCCs impose **no** potential constraints. They cannot occur in any perfect matching other than the baseline self assignment, and baseline edges are inside SCCs. More precisely an arc i -> j is allowed in some perfect matching iff it is a self-loop or lies on a directed cycle, equivalently its endpoints lie in a common SCC.

### Proof

Any directed simple cycle i_0 -> i_1 -> ... -> i_{k-1} -> i_0 permits moving report m(i_l) to job i_{l+1}, leaving all other baseline pairs untouched. This is a bona fide graph perfect matching. Its output difference is exactly XOR_l w(i_l,i_{l+1}); hence (1) implies (2).

Conversely any matching M determines a permutation of baseline report owners to their new destination jobs. Its disjoint permutation cycles are directed cycles of D. The output difference telescopes as the XOR of the weights of these cycles. Therefore (2) implies (1). This argument uses **one common matching over the whole trace**, never separately chosen packet explanations.

If potentials exist, the vertex potentials cancel around every cycle, giving (3) implies (2). If every directed cycle has zero weight, every closed directed walk has zero weight by decomposition into simple cycles. Within an SCC choose a root r and a directed root-to-i path P_i, and define p_i as its path weight. Given arc i -> j and any directed return path Q_j from j to r, the closed walks P_i+(i,j)+Q_j and P_j+Q_j have zero weight. XOR their equations to obtain p_i+w(i,j)+p_j=0. This proves (2) implies (3).

## Constructive certificate and failure witness

1. Construct E by exact timestamp/window comparisons, then find M0 by augmenting paths.
2. If no perfect matching exists return **NO_GRAPH_MATCHING / model-or-evidence inconsistency**. Do not exploit universal quantification over an empty set to announce success. A Hall-deficiency witness can optionally be added; the supplied implementation returns only this diagnostic status.
3. Build D and its SCC partition. Pick one root per SCC and choose directed paths P_i from the root and Q_i back to the root.
4. Set p_i = weight(P_i). Check first weight(P_i+Q_i)=0 for every i. Check next p_i+w(i,j)+p_j=0 for every internal arc. If all tests pass return **CERTIFIED** with M0, its role-parity vector, SCCs, and potentials. These data can be independently checked: verify M0; recompute D/SCCs; verify all internal equations; recompute the output. Recompute SCCs rather than trusting a supplied partition that could improperly split cycles.
5. A failed first test supplies a nonzero closed walk P_i+Q_i. A failed arc test, after the first tests pass, supplies nonzero walk P_i+(i,j)+Q_j. Decompose that walk into directed simple cycles by removing a segment whenever a vertex repeats. At least one component cycle has nonzero weight. Flip that cycle in M0 to obtain M1, a second actual **graph matching** with y(M1) != y(M0).
6. Return **UNRESOLVED** with M0,M1 and the nonzero cycle. These witnesses disprove constancy on the overapproximation, not physical identifiability. Neither, one, or both witnesses may be physically feasible. A physical NO needs separately verified feasible physical worlds with different output, not graph membership alone.

A potential mismatch by itself need not display a simple cycle. The closed-walk decomposition in step 5 is necessary to turn the failure into a valid matching flip.

## What it accepts without full identification

* Within-role ambiguity: two same-role jobs, both compatible with both reports, bits (0,1). Both matchings yield the same role XOR 1.
* Equal-payload cross-role ambiguity: roles A,B, complete 2-by-2 graph, bits (1,1). Both matchings yield (1,1), despite cross-role allowed edges.
* Genuine cancellation beyond both shortcuts: roles (A,B,A,B), bits (1,1,0,0), compatibility rows [{0,3},{1,0},{2,1},{3,2}]. Only the identity and the four-cycle are possible. Both give (1,1); all nontrivial cycle arcs cross roles and payloads are not all equal.
* An isolated cross-SCC compatible edge cannot occur in any matching and must not cause rejection.

Role purity of all allowed edges is sufficient, not necessary. Requiring purity of every raw compatible edge is still stronger because it also includes forbidden cross-SCC edges. A role's XOR over all jobs is not a per-job label reconstruction claim.

## Resource accounting

Let m=|E| <= n^2 and g be the number of distinct roles actually represented (g<=n). Charge g-bit XOR/comparison as O(g) bit operations, or O(ceil(g/wordsize)) word operations. Roles must be compressed to represented labels before creating basis masks; a numeric role name of size 2^B is not a request for 2^B-dimensional vectors.

The reference checker uses at most n breadth-first augmenting searches: O(n(n+m)) scalar graph operations. D and SCCs take O(n+m). Its deliberately simple explicit path storage and return-path weight computation cost O(n^2) vertices and O(n^2 g) bit operations, plus O(mg) for arc equations. Each failure walk has length O(n), and its simple-cycle decomposition/flip is polynomial. Consequently a conservative bound for the graph phase is O(n(n+m) + (n^2+m)g) elementary index/vector operations, with index accesses requiring O(log n) bits. Its memory is polynomial, O(n^2 + m + ng) index/vector storage; more economical parent-tree implementations are possible. No enumeration of all matchings is used by the checker.

For raw rational timestamps/endpoints with at most B-bit numerators/denominators, constructing E uses n^2 exact comparisons with polynomial bit cost (cross multiplication of B-bit integers). Interval construction from the learned physical model is a separate obligation: it must itself have polynomial representation/construction cost if an end-to-end polynomial claim is made. Arbitrary real-number oracles, unit-cost arbitrarily long timestamps, unbounded observation lengths, and uncharged learning/probe costs do not establish polynomial complexity. Include n,g,m,B, identifier lengths, payload input length, learned-model encoding and learning/query costs in any total-input accounting. The example code accepts exact integers/Fraction values; floating-point inputs are not a proof of exact boundary membership.

## Artifacts and verification

`binding_checker.py`: standard-library implementation, `check(edges, roles, bits)` and `from_windows(windows, timestamps, roles, bits)`. `verify_positive` independently validates positive witnesses, recomputes SCCs, and rejects tampered potentials.

`test_binding_checker.py`: positive/negative edge cases, timestamp ties with exact fractions, all 512 three-by-three compatibility graphs with all 8 binary role assignments and all 8 bit assignments (32,768 instances), plus 400 seeded random instances on n=4..7. Test oracle enumerates matchings solely for small-instance validation. All five test groups passed locally (including independent positive-certificate verification and tamper rejection). The exhaustive tests establish agreement on those finite cases; the proof above supplies the general theorem.
