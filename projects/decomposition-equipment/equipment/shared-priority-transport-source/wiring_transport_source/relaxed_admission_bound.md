# Local-information obstruction with unrestricted sequential same-tick commits

31 October 2026. Independent proof. This removes the one-commit-per-tick restriction from the growing obstruction. The resulting risk bound is sufficient and generally not sharp. The pair-probe repair remains unchanged.

## Model and admitted policies

Use n distinct-role modules, productive demand Q>0, diagnostic demand 2Q, zero callback lag, independent fresh fair invocation bits, and a persistent uniformly unknown strict module priority pi. Legal request times are multiples of R=nQ. Required productive jobs become available at time zero; each must run once, cannot be prefetched/replaced/rerun, and completion including the physical tail is required by H=nQ+gamma with 0<gamma<Q. The actual priority is one fixed world; uniform pi is only the lower-bound averaging distribution.

Unlike the stricter batch variant, arbitrarily many sequential atomic commits at tick zero are allowed. The first nonempty commit can start a job immediately; subsequent commits at the same tick queue behind that nonpreemptive running job. There are no productive callbacks before Q. Thus all tick-zero commit choices can depend on prior local-only observations and private randomness, but not new productive results. The raw API supplies no priority-dependent immediate acceptance/busy/status side channel. Clock and submission costs obey the same supplied bounds; granting free same-tick commits only makes this lower-bound comparator stronger.

Prior local-only experiments never leave work pending in two modules simultaneously. Their complete histories are independent of pi. Condition on that history and the controller's private seed: all pre-first-callback actions, including the first committed subset, are now fixed and independent of pi.

Any successful policy admits all required jobs at zero, since the next legal release R completes no earlier than R+Q>H. Their total demand is nQ. Every additional completed job before their completion adds at least Q and misses H. Positive residual calibration work likewise costs at least Q, by the Q-grid endpoint argument. Certified empty initialization is an alternative. Calibration callbacks exactly at zero can be included in the conditioned, priority-blind local history; they convey no new priority information.

Let S be the set of productive modules present in the first nonempty commit. If S is empty, a nonproductive job starts and success is impossible. Extra jobs in a commit can only eliminate successful worlds; on every successful world the first job is productive, from S, and is the highest-priority member of S. All remaining productive jobs are queued at zero before the first completion. Consequently, on every successful world their service order equals

    f_S(pi) = (min_pi S, then pi with that element deleted).

This statement need not hold on failed worlds with intervening extra jobs. For an upper bound extend the formula to all pi: allowing the corresponding idealized productive-only execution can only increase success. No illicit conditioning on the success event is used.

## Multiplicity bound

Fix nonempty S of size s and an output permutation sigma. It has a preimage only if its first element a belongs to S. Every preimage pi is obtained by inserting a into the tail sigma_2,...,sigma_n before every other S member. There are at most n−s+1 such insertion positions: the earliest of s−1 other S members has tail rank at most n−s+1; for s=1 all n positions are possible. Thus

    Pr(f_S(pi)=sigma) <= (n−s+1)/n!.

For an observed rank-bit word y with k ones, a given physical role-bit vector is compatible with exactly k!(n−k)! arbitrary service permutations, or fewer after restricting the first element to S. Since productive bits are independent fair, y is independent of pi even though f_S depends on pi. Therefore any controller's conditional success is at most

    min(1, (n−s+1)/binomial(n,k)).

This includes randomized commands by convexity. Averaging over the fair bit word gives the general bound

    success <= 2^(−n) sum_(k=0)^n min(binomial(n,k), n−s+1).

For every s, using n−s+1<=n yields the simple unrestricted bound

    success <= [2+n(n−1)] / 2^n,                    n>=2.

It is nontrivial for n>=4 and tends exponentially to zero up to its polynomial factor.

### Slightly stronger bound separating singleton first commits

When s=1, the first job's identity is known and the remaining priority is a uniform permutation of n−1 modules. Conditional on the first bit and a tail with h ones, the tail role vector is uniform over binomial(n−1,h) possibilities. The exact average optimum is therefore

    success <= n / 2^(n−1) = 2n/2^n.

This is attainable by guessing a uniform tail permutation after forcing a chosen first singleton.

For s>=2, the multiplicity bound has n−s+1<=n−1; every interior binomial(n,k)>=n, so

    success <= [2+(n−1)^2] / 2^n.

Combining the two cases, valid for every legal local-information-only policy,

    success <= max(2n, n^2−2n+3) / 2^n,            n>=2.

The bound is 1 at n=2, 3/4 at n=3, 11/16 at n=4, and vanishes exponentially. It is not claimed sharp beyond the identified cases. Therefore some fixed priority world has combined missed/unsafe risk at least one minus this bound. Random/adaptive selection of S cannot improve the bound, because it holds after conditioning on each priority-independent local history and private seed.

## Exact hard-safe completion bound for productive-only commits

For this paragraph restrict production commits to the n required productive jobs, with no extra diagnostic invocations. The support of f_S is exactly every permutation whose first element belongs to S: each such sigma is its own preimage. Fixing any first element a, the remaining n−1 modules can appear in every order.

For distinct roles, if the tail word is not constant, two such orders give different required role vectors. If the tail is constant but the first bit differs, changing a between two elements of S also gives different role vectors. Thus:

- If s=1, only words with a constant tail can be commanded with zero risk. Their probability is 2^(2−n) (including n=2, where the one-bit tail is automatically constant).
- If s>=2, only globally constant words can be commanded with zero risk. Their probability is 2^(1−n).

A hard-safe policy may refuse on other words, but refusal is missed work. For productive-only same-tick strategies the exact optimal hard-safe completion probability is 2^(2−n), attained by forcing a first singleton and commanding only constant-tail words. This support argument is not asserted for arbitrary extra diagnostics: extra slow work can cause timing gaps in some priorities and thereby filter the observed evidence. The unrestricted combined-success upper bound above already covers such policies; no additional exact hard-safe optimality claim is needed.

## Consequences and boundaries

The n=2 atomic-batch obstruction does NOT survive this richer admission API: two sequential singleton commits at zero impose a known order and solve it without priority learning. The growing obstruction does survive from n>=3 under the stronger bound, and from n>=4 under the simpler multiplicity bound. There is no need to engineer a one-commit restriction to obtain a growing local-information insufficiency result.

This remains a local-information-only result. Safe joint slow/fast comparisons identify priority and defeat it, intentionally. It is not an impossibility theorem over all safe commissioning experiments, an exact optimum for general first subsets, or a lower bound for arbitrarily fine release grids.
