# Native common-construction finite exact checks

Run `python reproduce.py` (Python 3, standard library only). This copies the
verifier and frozen expected JSON to a fresh temporary directory, then executes
both normal Python and `python -O`, requiring identical outputs. `require`
checks are explicit and are not disabled by optimization. All quantitative
arithmetic uses `fractions.Fraction`. No floating-point tolerances or LP solver
are involved.

## Coverage

* Four binary controls share Q = [[4/5,1/5],[1/5,4/5]] and w=(1/2,1/2).
  Inverting Q gives a unique candidate T. Independent, interior, boundary and
  infeasible sharp cases separate feasibility, exact full support and factor
  rank. Their native state counts are respectively 3, 4, 4 and impossible,
  using the two-stage theorem's two control states plus factor rank.
* Positive native factors check root normalization, row-stochastic links and
  emissions, observed joint law and coarse marginal. For these nonzero 2×2
  matrices, ordinary rank equals nonnegative rank: rank-one nonnegative matrices
  factor with one state, and the identity factor gives the rank-two upper bound.
* The sharp control explicitly violates the dual inequality: -9/10 < -4/5.
* Exhaustive enumeration covers every one of the 81 pairs of row-total Boolean
  2×2 Q,R. The maximal compatible relation criterion matches brute-force
  feasibility. There are 29 feasible pairs, 52 infeasible pairs and 63 feasible
  T witnesses. The optimal Boolean factor rank is one for 9 pairs and two for
  20. Rectangle-cover rank is also checked by direct factor enumeration.
* Ninety-six comparison squares include identities, permutations, deterministic
  announcement/output collapse and genuinely stochastic announcement/output
  maps. Factor transport, normalized native construction and support transport
  are verified. Ninety-six two-stage comparisons equal their directly composed
  comparisons exactly. Three additional cases collapse the coarse state space
  and output space together, checking a noninvertible state comparison.
* Nine factorization-arrow transport checks use a noninvertible latent-state
  merge, checking both factorization equations and support after transport.

The script can regenerate the frozen JSON using `python verify.py
--write-expected`; this is a maintenance command, not independent validation.

## Limits

These are finite regression checks, not proofs of the general construction,
LP duality, relative-interior characterization or complexity statements. No
arbitrary nonnegative factorization problem is solved. The exact-support
obstruction uses uniqueness of T in a fixed invertible binary example. The
comparison checks do not establish an arbitrary lifting theorem; they validate
explicit compatible diagrams. Native state counts invoke the scoped tagged
two-stage theorem, not arbitrary hidden-system minimality. The qualitative
rank-one witness need not lift quantitatively, even when its exact support does.
