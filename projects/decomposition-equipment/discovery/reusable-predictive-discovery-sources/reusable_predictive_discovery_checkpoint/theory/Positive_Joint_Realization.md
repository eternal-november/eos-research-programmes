# Positive joint recursive realization: supporting certificate module

## Plain-language abstract

Separate component predictors can each be valid without fitting together under the same communication and randomness budget. A certificate must specify which information each component receives and how one jointly sampled source drives all components. This note supplies an exact finite certificate for that implementation requirement. Its mathematics is established local-polytope theory; the research burden lies in discovering executable interfaces from evidence and certifying their predictive accuracy, not in renaming this criterion. A small crossing example shows an additional cost: two coarse decompositions each need a binary shared source, while their joint refinement needs a three-valued source.

## 1. Declared executable protocol

Fix finite component index set I, local context alphabets C_i, and output alphabets O_i. A discovered, executable observer has state q. Before each step, component i receives exactly context c_i(q,a); the delivery program, clocks, action visibility and observer memory are charged separately. Let C_* be the actually certified set of joint context tuples (possibly a proper subset of the Cartesian product).

The predictor uses fresh shared randomness R each step, independently of prior predictor execution and external actions. Given R, components may also use independent private randomness. No component may inspect another component's context except through the declared delivered messages. Output is o=(o_i). A fixed deterministic observer update q'=U(q,a,o) closes the recursion. Initialization is separately supplied and charged; runtime access to q is not automatically free or globally available.

This is a proposed stochastic predictor, not a claim that the actual environment has fresh innovations. Persistent environmental correlations must be captured by q or reflected in the predictive error certificate. In particular, a hidden persistent seed cannot be silently resampled each step.

## 2. Exact shared-response polytope

Let Sigma=product_i O_i^{C_i}. For sigma=(f_i), define V_sigma(o,c)=product_i 1[o_i=f_i(c_i)]. Then a conditional kernel K has a finite local realization with shared randomness independent of the inputs exactly when

    K(o|c) = sum_sigma mu_sigma V_sigma(o,c),  mu>=0, sum mu=1,

for all c in C_* and o. This is an LP when no bound is imposed on source support. Each vertex specifies all counterfactual local responses, not just the responses at one currently observed context. The SAME mu is used across contexts.

Proof. Sampling sigma implements the displayed kernel. Conversely, conditional on a shared source value r, let each local channel be L_i(o_i|c_i,r). A local randomized channel is a mixture of deterministic tables: sample its complete response table with weight product_{c_i} L_i(f_i(c_i)|c_i,r). Independent sampling of these tables conditional on r gives a distribution on Sigma with the required kernel. Integrate over r. This also covers continuous sources by their induced distribution on the finite table set.

Important source-cost distinction. Determinization can increase the shared seed alphabet by moving private randomness into the shared seed. Thus the theorem is exact for unrestricted finite shared randomness, NOT for a fixed cardinality r of a shared source when private randomness remains free. That bounded problem is

    K(o|c)=sum_{z=1}^r lambda_z product_i L_i(o_i|c_i,z),

with normalized local channels. It is nonconvex. Sparse support in the deterministic-table LP is a sufficient bounded implementation, not necessary for the same cardinality with private randomization.

## 3. Certificate size and checking

Flatten each V_sigma over certified (c,o), and let d be their affine dimension. Caratheodory gives a realization with at most d+1 deterministic strategies whenever the LP is feasible. A safe bound is d <= |C_*| (product_i |O_i|-1), because each context row is normalized. One may compute the exact affine rank to improve this bound. The deterministic-strategy universe has cardinality product_i |O_i|^{|C_i|}; the theorem is not an efficient discovery claim.

A sparse supplied certificate is checked by summation on all certified entries and checking normalization/nonnegativity. Its executable memory must include storage of q, response tables or their circuits, a shared-source generation/distribution mechanism, and all required messages. Arbitrary real probabilities are mathematical specifications; physical sampling and finite precision require additional error/resource bounds.

Farkas separation of the LP gives a linear inequality valid for all local kernels. This excludes the declared communication protocol, not all physical implementations. A centralized observer of all actions may implement kernels excluded by that protocol. Bounds on this implementation class do not identify the actual environment architecture.

## 4. Recursive interpretation and quantifier boundary

Given the initialization, U, c_i and mu, the construction defines one normalized controlled trajectory law for every causal controller whose actions lie in the declared family. Recursion follows simply by composing normalized kernels. No per-controller re-fitting is needed. This establishes existence of a positive recursively executable predictor; it does NOT establish agreement with data-compatible environments.

The main evidence theorem must separately bound prediction discrepancy for every admitted environment law, with that law held fixed throughout an episode. The strong reusable certificate has the order

    exists executable (U, contexts, mu, initialization), for every p in evidence set, accuracy bound(p,predictor).

Replacing it by 'for every p exists a predictor' gives an ambiguity family, not one deployable predictor. An ambiguity family may be valuable but must retain its shared world parameter across histories. Arbitrary independent selection of its rows is a larger rectangular uncertainty class.

## 5. Crossing refinement can increase source budget

Let P be uniform on W={100,010,001}, emitted independently at each tick. There are no action inputs. For cut AB|C, sample C as a binary shared source with P(C=1)=1/3. If C=1, emit AB=00. If C=0, the AB component uses a private fair coin to emit 10 or 01. This is a positive recursive implementation with a binary source. Symmetrically AC|B has one. Both realize exactly the same entire iid process, not merely matching isolated marginals.

The common refinement A|B|C needs a shared source with at least three values if components only have independent private randomness conditional on that source. Indeed, nonnegativity and zero mass outside W force every positive-weight product component to have support contained in W. Any Cartesian product support containing two distinct points of W also contains a point outside W (combine their differing coordinates). Hence every product component is a point mass, and three positive-mass points require at least three source values. A three-valued source choosing the active coordinate achieves the bound.

Therefore: positive realizations of compatible crossing cuts do not imply a positive realization of their common refinement at the same shared-source budget. This example is elementary nonnegative tensor rank. It is a useful regression test for witness/resource transport, not evidence of a new tensor theorem. It also exposes why deterministic-table support and source cardinality with grouped private randomness must not be conflated.

The amplification is unbounded: for the uniform distribution on the n one-hot binary vectors, EVERY nontrivial bipartition S|S^c has a two-valued shared-source realization (choose the active side, then choose the active coordinate privately within that side), while the n-way atomic decomposition needs exactly n source values by the same Cartesian-support argument. This holds for every iid time horizon. A catalogue of all positive binary cuts therefore still does not certify a binary-source joint refinement. The source alphabet cost grows from 2 to n; its worst-case bit representation grows from 1 to ceil(log2 n), not n bits.

No persistence-memory lower bound is claimed here. The source is refreshed each tick, and the example deliberately isolates crossing/refinement cost.

## 6. Prior coverage and exact remaining research burden

The existing programme's Positive_Realization_Audit.md section 3 already gives the full-space local-polytope criterion, normalized positive-retraction completeness and its Bell-locality baseline. This note does not strengthen that static theorem. Its role is to provide explicit recursive implementation semantics, quantifiers and source-cost accounting for the new discovery theorem. A substantive advance must come from evidence-driven interface synthesis and controller-uniform guarantees, or a genuinely new tractable joint-realization class; this module alone is insufficient.

A separate scope limit: finite-horizon evidence over all causal laws cannot certify a finite-memory implementation for arbitrary future horizons. Compatible extensions can introduce arbitrarily delayed dependence. Persistent compact claims therefore require an explicitly restricted continuation universe, a finite target horizon, or a continuing validation obligation.
