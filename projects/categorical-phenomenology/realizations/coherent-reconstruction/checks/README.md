# Exact joint-realization checks

Run from the report directory:

```sh
./checks/run_checks.sh
```

Or run either interpreter mode directly:

```sh
python3 checks/joint_gluing_checks.py
python3 -O checks/joint_gluing_checks.py
```

Python 3.10+ and its standard library suffice. There are no third-party packages,
network requests, floating-point coefficients, numerical tolerances, solver calls,
or `assert` statements. A failed check raises `CheckFailure` and exits nonzero.
The shell runner requires both modes to match each other and
`expected_output.txt` byte-for-byte.

## What the executable verifies

For supplied local matrices `A_i`, `B_i`, allowed hidden tuples `E`, retained
coarse tuples `S`, and global `w,Q,R`, the script assembles the exact rational
linear equations in `Z[j,h,s]`:

- `alpha[j,h] = sum_s Z[j,h,s]`;
- `sum_{s:s_i=t} Z[j,h,s] = alpha[j,h] B_i[h_i,t]`;
- `sum_{h:h_i=u} alpha[j,h] = A_i[j,u]`;
- `sum_{j,h} Z[j,h,s] = w[s]`;
- `sum_{h,s} Z[j,h,s] Q[s,o] = R[j,o]`.

Every `Z` coefficient is nonnegative, and omitted entries mean zero. Data are
checked for normalization, nonnegative exact coefficients, the global observable
marginal, and consistency of
the local retained-state marginals with projections of `w`.

A feasible certificate is converted to middle states `(j,h)` only when
`alpha[j,h]>0`. Its global factors are

```text
A[j',(j,h)] = [j'=j] alpha[j,h]
B[(j,h),s]  = Z[j,h,s]/alpha[j,h].
```

The executable independently verifies `A C_i=A_i`, `B F_i=C_i B_i`, the global
coarse law, and the observable target. It then aggregates the implementation
back to `Z` and checks every coefficient. A noncanonical source with a middle
state shared by both announcements is also aggregated and verified. Middle
states are column positions; an auxiliary label need not be unique.

### Nine check groups

1. **Splitting is necessary; exact memory lower bounds.** Two singleton-hidden
   local mechanisms have uniform marginals on `Z_m`. For `m=2,3,5` and
   `epsilon=0,1/2`, the conditional joint profile is
   `beta_j(x,y)=(1-epsilon)/m * [y=x+j] + epsilon/m^2`, and
   `R[j,(x,y)]=beta_j(x,y)/m`. All global coarse masses are `1/m^2`.
   The canonical construction has `m` middle states. The minor using columns
   `(0,k)` has exact determinant `(1-epsilon)^(m-1)/m^(2m)>0`, so ordinary rank
   requires at least `m` middle states in any factorization. At `epsilon=1/2`
   every entry is positive. An unsplit singleton tuple would force `R=p*w`,
   which is checked not to equal the target.
2. **Boolean feasibility does not imply stochastic feasibility.** Both local
   `A` rows are `(1/2,1/2)`. The first local profiles are `(1/3,2/3)` and
   `(2/3,1/3)`; the second reverses them. Both coarse and hidden tuples are
   restricted to their diagonals. The Booleanized equations are checked
   directly with existential quantification. Rational profile-row differences
   force each hidden tuple mass to zero, contradicting its required `1/2`.
   Explicit rational multipliers of the complete linear system verify
   `0=-1/2`. Replacing the hidden diagonal by the two crossed tuples restores
   stochastic feasibility, also verified.
3. **Equal coupling does not imply a deterministic common profile cover.**
   One local mechanism has one uniform profile, another has two deterministic
   profiles, and both have the same complete coupling `(1/2,1/2)`. For the
   diagonal retained interface, a verified linear-combination certificate gives
   `0=-1`. A common source with a genuinely stochastic local comparison exists
   and is checked separately. The obstruction is specifically to the
   deterministic comparison/common-profile requirement.
4. **Three-piece retained-certificate coherence.** A two-announcement,
   three-bit fixture uses 16 unequal positive masses `1/136,...,16/136`.
   The code checks direct versus iterated pushforward, coordinate-projection
   matrix composition, local-selector squares, full-tensor reassociation, and
   exact posterior-ratio telescoping for nested restrictions.
5. **Randomized interface transport coherence.** The same three-bit fixture
   is transported twice using genuinely stochastic announcement, retained-state,
   and output channels `U,L,G`, together with hidden-tuple forgetting. The first
   announcement channel has rows `(3/4,1/4)` and `(1/3,2/3)`; the second has
   rows `(2/3,1/3)` and `(1/4,3/4)`. The code checks the input transport squares,
   direct versus iterated transformed data and `Z`, the identity `P'F=F_*P`,
   and all posterior initialization, retained-profile and local-selector
   equations. It then verifies exact telescoping against the composite
   announcement channel with rows `(9/16,7/16)` and `(7/18,11/18)`.
   A second chain has an identically zero intermediate announcement row;
   posterior composition still agrees after omitting all zero-mass states.
6. **Noncanonical aggregation and direction of the posterior arrow.** A
   three-state source with shared-announcement noise aggregates to the
   two-state normal-form certificate. Separately, forgetting a third hidden
   tag merges two distinct equality/inequality correlation profiles.
   `N(FZ)` has one state and `F(NZ)` has two; the posterior row `(1/2,1/2)`
   is a valid comparison from the former to the latter. The unique normalized
   matrix in the reverse direction fails the retained-profile equation.
7. **Independently selected pairwise glues need not extend.** `AB` and `BC`
   favor equality; `AC` favors inequality. All three pair certificates have
   consistent fair one-bit marginals and are individually feasible. Enumerating
   all eight triples proves the pointwise score is at most 2. The chosen pair
   laws require score 3 in the sharp case or `27/10` in the full-support noisy
   case, yielding an exact nonnegative-joint-law obstruction. Sharp fixtures
   omit zero-mass coarse cells, while the general validator allows them.
8. **The umbrella joint-witness requirement is additional structure.** A
   shared retained bit is fair. One local deterministic output copies it and
   the other flips it. Both separate stochastic links and both fair output
   marginals are valid; a standalone diagonal joint output distribution also
   exists. However, retaining both prescribed `(retained bit, local output)`
   laws forces the outputs to differ. Exact support enumeration gives no
   allowed atom; equivalently, three required probability-one events violate
   the pointwise score bound 2. An independent coupling of the retained bit
   and diagonal joint output is checked to satisfy those marginals while
   failing both prescribed pair witnesses. Thus ordinary marginal compatibility
   or separate native simulations do not supply the extra joint witness.
9. **Zero rows and negative controls.** Two zero `alpha` rows are omitted
   before division in one fixture. A second fixture permits an identically
   zero announcement row, a zero retained coarse mass, and an unused named
   local hidden state. Its seven zero `alpha` rows are omitted, leaving exactly
   two middle states without inventing any zero-mass conditional row. Wrong
   mass, negative `Z`, a forbidden hidden tuple, a vacuous obstruction, and
   floating-point input are all explicitly rejected.

## What this does not claim

These are exact, reproducible witness and obstruction checks for the displayed
finite examples and algebraic constructions. They are not a proof by finite
testing of the general theorem, a general LP-feasibility solver, a general
nonnegative-rank solver, or a claim that arbitrary pairwise marginals extend.
The rank conclusion for the correlation family uses a verified ordinary-rank
minor lower bound together with an explicit matching upper-bound factorization.
The posterior coherence checks retain the full joint certificate; they do not
reconstruct lost higher-order correlations from marginal data.
