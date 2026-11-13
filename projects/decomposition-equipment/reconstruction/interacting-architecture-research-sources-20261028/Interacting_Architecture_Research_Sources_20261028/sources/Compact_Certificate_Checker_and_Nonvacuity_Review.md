# Independent checker audit and a nonvacuous state-emitting family

## Result first

The calibrated-control algebraic certificate route is correct, subject to the qualifications in `Compact_Certificate_Independent_Review.md`. I independently checked the reachability and invariant-subspace arguments. This note adds two substantive findings:

1. **Small observable rank is not restricted to physically irrelevant coordinates, even with ordinary diagonal state emissions.** There is an explicit strictly positive invertible drift on `n` binary components, rich local controls, and observation of one bit, with controlled Hankel rank `2n`. All `2^n` point states have distinct controlled future laws. Its shared one-step branch selector has `2n+1` modes and is charged explicitly, not treated as communication-free.
2. **The checker is cheap relative to a specified witness grammar and a certified contraction order.** Soundness does not itself require proving the strong hypotheses that guarantee witness existence. Explicit output-alphabet size, exact coefficient encoding, zero-probability histories, and whether the initial law is being replaced all need to be stated.

The state-emitting example below was checked with exact rational arithmetic for `n=3`; the general proof is elementary. This is a nonvacuity example for a restricted certificate theorem, not an architecture-discovery algorithm, a generic low-rank claim, or a novelty claim.

## 1. Scope of the algebraic agreement

Use column laws, nonnegative letter operators `H_(u,y)`, and column-stochastic totals. The assumptions are

    sum_y H_(0,y) = D,
    sum_y H_((i,k),y) = D K_(i,k),

where `D` is invertible, `K_(i,k)` acts on coordinate `i` only, and the local real span, including identity, is all matrices whose column sums are equal.

Both the reachable column span and observable row span are invariant under `D`; finite dimensionality and invertibility make them invariant under `D^-1`. They are consequently invariant under every local equal-column-sum algebra. Products of local point resets in this *linear algebra* give full column reachability from any normalized initial law. The row space is a downward-closed direct sum of tensor constant/contrast blocks. Its product-function basis gives a signed canonical-polyadic quotient tensor of rank exactly `r`, the Hankel rank. This is not nonnegative CP and not a claim of complete positivity.

Strictly positive invertible local stochastic controls can span the required algebra: take a positive invertible stochastic interior point and sufficiently small independent zero-column-sum perturbations. The resulting *signed linear combinations* include resets; the physical controls themselves need not reset anything. This remains strong calibration information.

### Why an initialized law does not normally give an all-state quotient

A length-`m` fair-bit shift register gives a direct counterexample without the calibration hypotheses. Emit its first stored bit, shift left, and append an independent fair bit. From the uniform product initial law, the entire output process is iid fair and has Hankel rank one. From a deterministic register state, however, its first `m` outputs are prescribed by that state, so different register states have different future laws.

A normalized one-dimensional quotient would have to be `F=1^T` (up to scalar coordinate gauge). But `1^T H_y` is the indicator that the first stored bit equals `y`, not the constant row `(1/2)1^T`; the required all-state intertwining identity therefore fails. The register drift is noninvertible and there are no rich calibrated controls, so this does not contradict the positive theorem. It shows exactly why initial observational agreement alone is not enough to demand an all-state quotient of initialized rank.

## 2. State-emitting rank `2n` with no irrelevant bit

Let `n >= 2`, let `x=(x_0,...,x_(n-1))` be binary, and put `N=2^n`. For nonempty `S`, write the Walsh row

    chi_S(x) = (-1)^(sum_(i in S) x_i).

Let

    C = {{0}} union {{j},{0,j}: 1 <= j < n},
    q = |C| = 2n-1,
    W = span{1, chi_S : S in C}.

Thus `dim W = q+1 = 2n`. Its interaction ideal contains the empty set, every singleton, and the pairs `{0,j}`, but no pair of distinct noncentral sites.

Choose any cyclic permutation `sigma` of `C`. Define the stochastic parity channel

    M_(S,T)(x'|x) = (1/N) [1 + chi_S(x') chi_T(x)].

For fixed `x`, this is the uniform law on the output states having parity `chi_S(x')=chi_T(x)`. It is nonnegative, column stochastic, and also row stochastic. It can be sampled by drawing all but one output bit fairly and setting the last bit of `S` to enforce the parity. Here `|S|,|T| <= 2`, so only a constant-size parity operation is needed after choosing the branch.

Let `J` be uniform resampling and set

    gamma = 1/(4q),
    D = (1/2) I + (1/4) J + gamma sum_(S in C) M_(S,sigma(S)).

The weights sum to one. Every entry of `D` is at least `1/(4N)>0`. Walsh orthogonality gives

    chi_S D = (1/2) chi_S + gamma chi_(sigma(S))   if S in C,
    chi_T D = (1/2) chi_T                        if T nonempty and T not in C,
    1 D = 1.

Consequently `D` is invertible: on `span C` it is `(1/2)I + gamma P` with `P` a cyclic permutation, whose eigenvalues cannot vanish since `gamma < 1/2`; elsewhere its eigenvalues are `1/2`, apart from the constant eigenvalue `1`.

Observe the first bit *after* transition. With `E_y=diag(1{x_0=y})`, use

    H_(u,y) = E_y D K_u,

where `K_u` is identity or one of the calibrated single-site controls. Then `sum_y H_(u,y)=D K_u`, as required.

### Exact observable row space

`W` is stable under:

- every local equal-column-sum algebra, because its interaction family is downward closed;
- `D`, by the displayed Walsh formula;
- `E_0,E_1`, because multiplication by `chi_{0}` exchanges `1` with `chi_{0}` and exchanges `chi_j` with `chi_{0,j}`.

Thus the actual observable row space is contained in `W`. Conversely, the first observation gives `chi_{0} D`; summing over observations gives the unconditional map `D`. Powers of `D` generate all of `span C` from `chi_{0}`: `P` is one cycle and `D=(1/2)I+gamma P` has the same cyclic span. Equivalently, the observable row space is `D^-1` invariant and hence contains `chi_{0}`, followed by the whole cycle. Therefore it is exactly `W`.

Rich local controls give full hidden linear reachability for **every** initial probability law, so the initialized controlled Hankel rank is exactly `2n`. One may choose the uniform product initial law, which is stationary under idle drift because `D` is doubly stochastic.

Every singleton `chi_j` belongs to `W`. Hence distinct hidden point states differ on some future evaluation: all `2^n` point states have distinct controlled future laws. In particular, this is not merely a system with a few relevant bits plus wholly unobservable spare coordinates. It also does not assert that every mixed hidden law is distinguishable, or that `2^n` is the smallest state count of every alternative positive realization.

This disproves the stronger proposed collapse: diagonal emissions plus rich controls do **not** force the observable row space to be the full function space on a subset of coordinates. They do impose multiplication invariance for the available emissions. In this example only the central bit is directly emitted, and the proper downward ideal above is closed under that multiplication. If emissions separately supply nonconstant one-site functions of every coordinate, the full-rank collapse does occur.

### The shared selector is a real resource

The displayed positive implementation draws one shared branch from `q+2=2n+1` possibilities: identity, uniform resampling, and the `q` parity channels. The selector has `O(n)` states, costs `O(log n)` bits to encode, and its broadcast/dependencies are part of the supplied circuit. This is not an architecture with free independent local updates and no communication.

For verification, expand the `q+2` branches. Each parity channel itself has the product-matrix identity

    M_(S,T) = J + (1/N) chi_S^T chi_T.

Thus `D` has `q+2` product-matrix terms after combining identical `J` terms. A local actuation and the unary output indicator preserve this form. A squared residual with a rank-`s` CP quotient expands into `O(s^2(q+2)^2)` pairs of product terms; each pair contracts independently across the `n` sites. With binary sites, each local hidden-state sum has constant size. Hence the check is polynomial in `n,s` and coefficient bit lengths, explicitly counting the shared selector and all branch pairs. This provides a concrete low-verification-cost example without silently replacing one-step verification width by static graph width.

### Exact computational check

`check_state_emitting_compact_example.py` uses rational arithmetic for `n=3`, the cycle

    {0} -> {1} -> {0,1} -> {2} -> {0,2} -> {0},

and two positive invertible local controls per site, together with identity. It verifies local algebra span indirectly by the displayed family and directly closes both actual letter-operator spaces. Its result is

    hidden_dimension = 8
    predictive_rank = 6
    reachable_dimension = 8
    minimum_D_entry = 1/32
    determinant_D = 100001/12800000
    all_states_separated = True

## 3. What the exact checker establishes

Let the target be `(alpha, ell, {A_(u,y)})`, with column predictor coordinates. A supplied hidden stochastic circuit, quotient `F`, and initial law `mu` pass if

    F H_(u,y) = A_(u,y) F   for all labels,
    ell F = 1^T,
    F mu = alpha.

These equations give equality of all interventional controlled-word probabilities by induction. They imply the normalized predictor update

    z' = A_(u,y) z / (ell A_(u,y) z)

on positive-probability histories, with `z=F p` for the corresponding normalized hidden posterior. Conditional laws on zero-probability histories are not determined and need not be claimed equal.

The same word identities imply equality under every common adaptive randomized policy: multiply each controlled-word probability by the policy factors depending on the previous observed actions and outputs, then sum as appropriate. Do not confuse an intervention-fixed action word with ordinary conditioning on an adaptively chosen action sequence; selection effects can make those different objects.

### Initial replacement is only observational replacement

The affine normalization `ell F=1` places all columns of `F` in an affine space of dimension `r-1`. Carathéodory supplies a mixture of at most `r` product *point* laws with the same `F` image as an arbitrary correlated initial law. The certificate can therefore use such a `mu` when proposing an observationally equivalent realization.

This does not recover or preserve the original correlated physical law, and need not preserve hidden stationarity. If the task is to check a **specified** initial law `pi`, the checker must still establish `F pi=alpha`; it cannot silently replace `pi` by `mu` and claim to have verified the specified physical model.

### Positivity and normalization must be typed correctly

Local normalized kernels prove that the complete hidden transition is stochastic only when the supplied composition is a genuine generative stochastic circuit: an ordered composition, a directed acyclic sampling network, or another explicitly sound construction. An arbitrary loopy factor graph with locally normalized factors need not define a globally normalized stochastic kernel. Letter maps are substochastic; their sums over outputs are stochastic.

The quotient factors and the target matrices can be signed. Positivity of the actual word laws follows from their equivalence to the checked hidden stochastic realization, not from positivity of the quotient tensor.

## 4. Honest complexity parameters

For real entries, a residual is zero exactly when its squared Frobenius norm is zero. This converts an exponentially indexed identity to scalar contractions, but does not make arbitrary contractions inexpensive.

The witness must supply, or the promise must bound, an elimination order for the **actual expanded doubled residual network**. It must include identified input indices, both copies of the candidate circuit, the quotient factors, output indices if being summed, and any interfaces/branch selectors. Treewidth of a static physical interaction graph alone is insufficient. Complexity should be stated using the product of domains in the largest intermediate tensor, or an explicitly defined width and a maximum domain bound.

If every target matrix `A_(u,y)` is supplied explicitly, running time includes the number of action-output labels. A joint output alphabet can itself be exponentially large in the number of readouts. Avoiding hidden product-state enumeration does not avoid this input-size issue. A factored target output tensor can instead be used, but then its network and output variables belong in the verified contraction-width assumption.

Floating residuals do not prove exact equality. A bit-complexity statement needs exact rational or appropriately specified algebraic data and must count the supplied coefficient bit lengths. For rational tables, contraction intermediates can be represented with a common denominator formed from the input denominators; the logarithm of the number of summed assignments adds only polynomially to numerator bit lengths. This supports polynomial bit complexity when both the operation count and the explicit coefficient lengths are polynomial.

Polynomial CP parameter count alone is not a polynomial binary certificate. A rational certificate-size proof can use independent target future-test rows of length at most `r-1` to reconstruct rational `F`, fixed rational product bases to encode it, and a rational basic feasible solution for the sparse initial weights. This is an existence argument, not a polynomial-time procedure for finding those supports or the architecture.

## 5. Finite data and rank promises

A finite probability table by itself does not identify a globally valid rank-`r` controlled predictor. A claimed exact data-learned predictor requires an exact finite-rank/minimality promise, or a separate justified realization theorem. An empirical rank estimate and near-zero residuals do not replace it.

Under a genuine global rank bound, standard finite-dimensional span arguments justify finite word tests. For example, two linear representations of dimensions `r_1,r_2` that agree on all words of length at most `r_1+r_2-1` agree on all words; the bound follows from the reachable span of their direct-sum difference representation. Without a global dimension bound, a process may agree on every tested finite word and disagree later. Controlled word tables may themselves be exponential in the testing horizon and alphabet size.

Soundness of the intertwining checker does not depend on separately certifying full local control span or invertibility of `D`; those assumptions are used for the *completeness and size guarantee*. If a result claims to check that an input belongs to the promised calibrated class as well, global drift invertibility and its resource cost need their own treatment or a locally verifiable invertible circuit decomposition.

## 6. Audit of the separate clock/parity format obstruction

The proposed clocked reversible-circuit construction is sound with the following exact conventions. Use a circuit `C` implementing `(x,b)->(x,b XOR q_G(x))` while restoring the data-bit ordering, followed by its inverse. Clock length `L` is the full circuit length, and emit `1{t=0}b` **before** the selected gate. Every state has either the all-zero future stream or one periodic pulse at a phase. The observable all-state rank is `L+1`; uniform product initialization assigns mass `1/2` to the zero class and `1/(2L)` to each phase, and length-`L` output words isolate all these classes, so the initialized rank is also `L+1`.

At the halfway clock phase with `b=0`, the next phase-zero pulse equals `q_G(x)`. A normalized quotient to an arbitrary minimal target is an invertible linear transform of the class-indicator coordinates, not literally the class-indicator map in every chosen basis. A fixed linear functional on its predictor index nevertheless recovers the pulse indicator. Contracting this functional and fixing clock and `b` cannot increase CP rank or a TT bond rank.

Across a cut, the sign matrix `(-1)^q_G` has real rank `2^rho`, where `rho` is the GF(2) cross-adjacency rank: within-side quadratic terms only multiply rows and columns by signs; the remaining rows are distinct orthogonal binary characters. Since `q_G=(1-(-1)^q_G)/2`, its matrix rank is at least `2^rho-1`. A graph with linear cross-rank across every balanced data cut therefore forces an exponential TT bond in every data-variable order, even if the clock, flag, or predictor index is inserted elsewhere. A random-graph counting argument can establish existence; no efficient construction or recognition of that graph property should be inferred without more work.

This obstruction concerns CP/TT quotient witnesses, not every possible witness grammar. The same quadratic function has a polynomial Boolean circuit, and the clocked implementation has a polynomial local circuit. A one-step bounded-width circuit is compatible with a quotient tensor that has large TT rank. It also does not satisfy the rich local calibration assumptions of the positive theorem, so it is not a contradiction of that theorem.

### A noisy nonreset version is also valid

Independently flip the **one emitted output bit at each time** with fixed probability `epsilon` in `(0,1/2)`. The length-`L` binary symmetric channel is an invertible Kronecker power, so the columns associated with the `L+1` distinct noiseless class words remain linearly independent. This proves all-state rank `L+1`. Since `D^L=I` and every initialized class weight is positive, the same likelihood matrix, transposed and multiplied by the positive diagonal class weights, proves initialized reachable rank `L+1`.

In class coordinates, each symbol map is a phase permutation times a strictly positive diagonal matrix, hence invertible. Every finite output word has positive probability (at least `epsilon` to the word length), and no observed word gives a rank-one reset. The same class quotient, circuit decoder proof and CP/TT lower bound remain. Hidden drift is still a permutation; this is not an entrywise positive or mixing hidden-transition example. The exact small-instance timing script also checks the noisy ranks and symbol determinants at `epsilon=1/4`.

## Status

The algebraic certificate audit and the exact `n=3` nonvacuity test are complete. The first pass followed the author's precise hypotheses before the main draft existed. A final text-level pass of `Compact_Discovery_Certificate_Route.md` was completed on **2026-10-28, approximately 00:29 UTC**, covering its algebraic CP theorem, initialized-rank counterexample, clock/parity every-order TT lower bound, suffix/cancellation proof including the phase-zero boundary, and the `r=2n` family's physical and expanded-product branch counts.

That pass identified one resource-count correction, which the author applied: one active component does not by itself bound the number of available control labels. The text now explicitly limits each site's calibration family to `O(d_i^2)` labels, or charges for all additional labels. The initializer terminology was also changed to nonnegative so that sparse support is not excluded.

`check_clock_parity_timing.py` independently checks the decoder, emission and transition identities on a three-data-bit abstract-Toffoli instance with six clock phases and 96 hidden states. It finds exactly seven predictive classes, the required uniform initial masses (48 zero-class states and eight states per pulse phase), and the quadratic halfway slice. This test checks the timing/algebra, not the separate nearest-neighbor routing or large-cut-rank graph construction.

