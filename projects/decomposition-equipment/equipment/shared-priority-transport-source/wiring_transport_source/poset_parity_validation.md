# Independent poset parity validation

## Finding

The adjacent-rank interval lemma is correct. Its condition characterizes **invariance** of every role's XOR across all linear extensions. To certify a specified target vector, also check that one reference extension attains that vector.

The exact checker is strictly stronger than certification over all perfect matchings in the job–possible-rank graph. A smallest-size strict example has four jobs; none exists with at most three jobs (exhaustive binary roles and binary payloads).

## Constructive proof of the interval

Let jobs i,j be incomparable. Pred and Succ mean strict transitive predecessor/successor sets. Put D=Pred(i)∪Pred(j), U=Succ(i)∪Succ(j), and A=P\(U∪{i,j}). Both D and A are order ideals and D⊆A. In any extension with i,j at adjacent one-based positions k,k+1, all of D must precede the pair and all of U must follow it. Hence

|D|+1 ≤ k ≤ n−|U|−1.

Conversely, choose a topological order of D, followed by a topological order of A\D. Every prefix of this concatenation is an ideal. For any k in that interval take its first k−1 jobs, append i,j, then topologically order the remaining jobs. This is a linear extension; replacing i,j with j,i gives another. Thus every rank in the interval is achievable, including its endpoints.

Any two linear extensions are connected by adjacent swaps of incomparable jobs. One constructive connectivity proof repeatedly brings the next desired job leftward toward its position in the destination extension; every job crossed is incomparable, since comparable pairs have the same relative order in both extensions.

An adjacent swap changes role parity iff the swapped roles differ and the two rank payload bits differ. Therefore all role parity vectors are invariant iff each incomparable cross-role pair has equal adjacent bits throughout its achievable interval. When the test fails, the construction above gives two explicit valid extensions with different parity vectors. At least one violates any prescribed target vector. A matching reference vector plus invariance proves universal target compliance.

## Strict rank-matching gap

Jobs 0,1,2,3 have roles A,B,A,B. Relations are 0<3 and 1<2. Rank payload bits are (0,0,1,1). The six linear extensions are:

- 0,1,2,3
- 0,1,3,2
- 0,3,1,2
- 1,0,2,3
- 1,0,3,2
- 1,2,0,3

Each has role XOR vector (A=1,B=1). The rank-possible graph allows jobs {0,1} at rank 1, all jobs at ranks 2 and 3, and {2,3} at rank 4. The perfect matching (0,2,1,3) therefore passes individual rank feasibility but violates 1<2 and has parity (0,0). A conservative all-matchings sufficient checker cannot certify the target; the exact poset checker can.

## Executable contract

`poset_parity_checker.certify(n, edges, roles, bits, required=None)` accepts jobs 0..n−1 and arbitrary strict precedence edges, not necessarily transitively closed. Roles are hashable labels. Bits are binary. `required`, if supplied, maps each occurring role to its target bit.

- `CERTIFIED`: all linear extensions have the reported parity; it equals `required` when supplied.
- `NONINVARIANT`: `orders` contains two explicit extensions of different role parity.
- `TARGET_MISMATCH`: parity is invariant but the supplied target is wrong; `order` witnesses failure.

`poset_parity_verifier.verify` independently checks outputs, importing nothing from the producer. Failure verification uses only original precedence edges and direct parity sums. Positive verification recomputes transitive reachability using DFS (producer uses Warshall closure), checks the reference extension and target, then checks the proved boundary condition. It is a theorem-based polynomial verifier, not an independent proof of the theorem. Exhaustive permutation enumeration provides the separate empirical cross-check.

Run `python poset_parity_checker.py` to regenerate `poset_parity_test_results.json` and print progress. No third-party dependencies. Complexity with elementary set operations is at most cubic for closure and pair/rank checks, apart from exhaustive test harness.

## Coverage

All naturally labeled posets of sizes 1 through 5 are obtained by transitive closure and deduplication of all upper-triangular edge subsets. Counts are 1,2,7,40,357. For every poset, every binary role assignment and every binary rank-payload assignment is tested against every linear extension enumerated independently from all permutations: **376,292 cases**. Every reported failure witness is validated against original edges. Every incomparable-pair adjacency interval is compared to its exact observed attainable ranks; all **4,127** rank constructions are checked explicitly. Reverse-label versions of every poset are additionally checked with distinct roles and all payloads (**12,130 cases**). Target compliance, target mismatch, and cyclic-input rejection receive dedicated checks.

Scope: finite combinatorial scheduling and executable certificates only. No physics claim. Any connection between job ranks and delivered messages requires the separate model's delivery assumptions (e.g. one productive job per module and delivery lag bounded by J below the minimum next-job delay).
