# Optional null ideal amalgamation obstruction

31 October 2026. Mathematical appendix extracted from the original I1 scope note, section 5. This is separate from the central partial-map family, where B remains faithful. The coefficient obstruction holds for every n≥2. Its graph-level visibility requires N≥1 and a nonempty interface category K, so that a nonempty graph color exists; no such visibility is asserted at empty K or N=0.

For every n≥2, define K_n={1,0,x_i : i∈Z/n}, with 1 the identity, 0 absorbing and x_i x_j=0. Define A_n=K_n∪{p}, with p²=p and p x_i=x_i p=x_0, p0=0. Define B_n=C_n∪{0,x_i}, where s^0=1, s^j x_i=x_i s^j=x_(i+j), and all products in the null ideal remain zero. K_n embeds literally in both.

Associativity: A_n is a null ideal acted on by the two-element idempotent monoid {1,p}, whose p-action is the constant retraction to x_0 (and fixes 0). B_n is the same null ideal acted on by the cyclic group via shifts (fixing 0). The left and right actions commute in each local monoid. Products of two ideal elements are zero, so all remaining triple cases vanish. Their multiplication-table presentations are terminating by length and confluent by associativity; both inputs are individually convergent.

In ANY common target identifying K_n, associativity gives

    p(x_i s^j) = p x_(i+j) = x_0,
    (p x_i)s^j = x_0 s^j = x_j.

The raw union of local multiplication-table reductions has the mixed peak p x_0 s^j: left-first reduces to x_j, while right-first reduces to x_0. For j≠0 these are distinct irreducible common letters, so the union itself is not confluent. Hence all n distinct shared elements collapse in BOTH inputs under the generated congruence. No additional mixed relation was imposed. Lift to P[A_n] ← P[K_n] → P[B_n]; the shared theory contains both the nontrivial old graph/interface P and genuine shared coefficients K_n. The unary identity of any nonempty graph exhibits the collapse, and the diagonal law propagates it to nonempty branches of the six-vertex example. This is an unbounded lost-information family (one fibre has size at least n), not repetition of one finite fixture.

Attribution: the basic nonembeddable finite-semigroup mechanism is classical; Jackson, *The embeddability of ring and semigroup amalgams is undecidable*, J. Austral. Math. Soc. 69 (2000), p.273, gives two four-element semigroups sharing a three-element null semigroup, with associativity forcing two shared entries equal. Primary source https://doi.org/10.1017/S1446788700002214. The n-family below is not a claim of discovering nonamalgamation.

An exact conservative repair preserving BOTH these input monoids and the SAME full interface identification is impossible by the displayed equation. Useful repairs must name what is changed: retain only old P as the common interface (do not alias conflicting x_i), yielding the positive commuting product comparison A_n×B_n with both inputs retained; or modify one local action with explicit permission. If keeping full K_n is mandated, reject composition rather than silently quotient local distinctions. The former repair preserves local inputs and old graph interfaces but deliberately weakens the additional shared-coefficient identification.
