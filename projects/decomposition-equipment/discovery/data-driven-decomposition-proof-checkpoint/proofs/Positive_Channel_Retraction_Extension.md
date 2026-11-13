# Positive channel retractions: a complete nonsimplicial subclass

Status: proved finite-dimensional extension of the channel-cone criterion; independent AI proof review passed after the stated repairs. No Lean or external human verification is claimed. This is standard positive-projection and finite local-polytope machinery applied to the inferred operational frame, not a claim of a new primitive mathematical mechanism or completion of general spatial discovery.

## Readable abstract

The first cone test worked only when a uniquely readable list of local mechanisms existed. Here the local list can be redundant. We compute all its extremal mechanisms and solve for a positive joint distribution over them. Ordinarily, failure of that search would not rule out a realization using mechanisms outside the observable local span. A checkable positive retraction removes that loophole: it converts every such outside mechanism into one on our list without changing the joint behavior. With that extra certificate, the search is complete. The test can accept correlated nonsimplicial examples that the first test rejected, and can genuinely reject other behaviors with exactly the same local geometry.

This remains a test on a candidate operational frame reconstructed upstream, not a general solution to discovering unknown state spaces or arbitrarily crossing frames. Its computational cost can be exponential.

## 1. Setting

Use one positive-probability public transcript (v,m,b) from Observable_Channel_Cones_and_Minimal_Deterministic_Ports.md. All statements in this note are conditional on that fixed transcript. We have a normalized non-signalling finite channel

    H(y_1,...,y_k | x_1,...,x_k),

with full product nonempty private input alphabets and fixed nonempty finite output alphabets. Private commands are included in x_i when permitted by the original protocol; H's shared instruction law is not allowed to depend on those residual inputs. Let U_i be the span of the mode-i unfolding of H, mode i indexed by (x_i,y_i).

Let W_i be the real vector space of all local tables L(y_i|x_i) whose row sums are constant across x_i. Let ell_i(L) denote that common row sum. Its positive cone is

    D_i = W_i intersect entrywise-nonnegative tables.

The normalized base ell_i=1 is exactly the full local stochastic-channel polytope. Its vertices are deterministic channels d_f(y|x)=1[y=f(x)], for every function f:X_i→Y_i. Consequently D_i is generated conically by those finitely many d_f.

Non-signalling gives U_i subset W_i. Let C_i=U_i intersect D_i. This is a pointed, spanning polyhedral cone with strictly positive ell_i away from zero. Enumerate ALL its extreme rays and normalize them to ell_i=1:

    A_i = [L_i,1 ... L_i,s_i].

No simpliciality or linear independence is assumed. These are discovered local channels, not supplied generators.

## 2. The restricted-span LP is always exact for its stated class

Solve the finite feasibility problem

    H = (A_1 tensor ... tensor A_k) G,
    G >= 0.

Here G has one coordinate for each instruction tuple (r_1,...,r_k), and the tensor equality is equality of all input/output entries. Its normalization sum G=1 follows automatically by summing over all outputs at any fixed input tuple. It may harmlessly be imposed as a redundant equality.

Proposition. This LP is feasible if and only if H has a finite local shared-randomness representation whose local stochastic generators all belong to U_i.

Proof. A feasible G is such a representation. Conversely, expand each normalized local generator in the normalized extremal channels of C_i. Since ell_i=1, its nonnegative coefficients sum to one. Substitute all expansions in the assumed positive joint representation and collect instruction tuples. The resulting G is nonnegative and reconstructs H. QED.

This proposition alone is NOT completeness for arbitrary local generators in W_i. In particular, a negative LP verdict cannot otherwise exclude positive mechanisms outside U_i. Linear projection into U_i generally does not preserve positivity.

## 3. A computable certificate that removes the restriction

A normalized positive retraction is a linear map

    P_i: W_i → U_i

such that:

(a) P_i u = u for every u in U_i;
(b) ell_i(P_i w)=ell_i(w) for every w in W_i;
(c) P_i(D_i) subset C_i.

Condition (c) is equivalent to entrywise nonnegativity of P_i d_f for EVERY deterministic local channel d_f. Hence existence of P_i is a finite linear feasibility problem: parameterize its output in a basis of U_i, impose (a) on a basis of U_i, impose (b) on a basis of W_i, and impose P_i d_f >= 0 for each deterministic vertex. All constraints are linear in the matrix entries of P_i.

The output-range condition is built into the parameterization, not inferred from positivity. Condition (a) makes P_i idempotent automatically. If input spaces and H have rational coordinates, this is a rational LP; a feasible rational certificate can be checked exactly.

The number of deterministic vertices is |Y_i|^|X_i|. This is an intrinsic finite test, not a polynomial-time promise. One can use separation or structural symmetries when available, but no such efficiency is assumed here.

### Complete-class theorem

If every mode admits a normalized positive retraction P_i, the all-extreme-ray core LP in Section 2 is feasible if and only if H admits ANY finite local shared-randomness realization with stochastic local channels and no transmission of residual private inputs.

Proof. Sufficiency is Section 2. For necessity, suppose

    H = sum_lambda p_lambda tensor_i K_i,lambda,

where p_lambda >= 0, sum p_lambda=1, and each K_i,lambda is an arbitrary row-stochastic local channel in W_i. Every mode fiber of H belongs to U_i, so acting with P_i on that mode fixes H. Thus

    H = (tensor_i P_i)H
      = sum_lambda p_lambda tensor_i P_i(K_i,lambda).

By positive normalization preservation, every P_i(K_i,lambda) is a row-stochastic channel in C_i. Section 2 then supplies a feasible G. QED.

All maps act on different tensor modes, so their application order commutes. This is NOT a claim that positive retractions attached to two different overlapping physical frames commute.

A shared random variable with a continuous law gives no larger class here: finite-dimensional local channel polytopes allow expansion into the finitely many joint deterministic strategies, producing a finite convex representation.

### Port consequence

Apply the theorem to every used public transcript of the canonical deterministic-message quotient. If retractions exist and every core LP is feasible, the protocol realizes K and attains its componentwise minimal deterministic outgoing messages. If a retraction-certified core LP is infeasible for one used transcript, that canonical-minimal-message protocol is impossible even with arbitrary finite shared randomness and arbitrary local stochastic generators. Larger messages, a different candidate frame, or a different communication architecture are NOT excluded.

Retraction failure itself proves none of these impossibilities: it means this completeness certificate is unavailable. The simplicial direct-unmixing theorem remains separately applicable and does not require an ambient retraction.

### Dual obstruction and refinement of the architecture

If the core LP is infeasible, finite-dimensional Farkas separation supplies a linear functional w on joint input/output tables with

    w(product_i L_i,r_i) >= 0 for every instruction tuple,
    w(H) < 0.

This is an exact certificate against the restricted generators. For evaluation on arbitrary empirical tables, first choose any linear extension of each P_i from W_i to the ambient space of all local tables, agreeing with P_i on W_i. No positivity outside W_i is asserted or required; the resulting coefficient norm depends on this choice. Under the retraction certificate define the lifted functional

    w_full(T) = w((tensor_i P_i)T).

Every product of arbitrary local stochastic channels is sent into the cone generated by the tested products, so w_full is nonnegative on ALL local shared-randomness behaviors. Meanwhile w_full(H)=w(H)<0. Thus the same calculation yields an obstruction independent of a hidden choice of local generators, not merely failure of a preferred basis.

For a fixed proposed frame and protocol, this is also a robust separation certificate. If w_full(H_hat)=-gamma<0 and every possible true conditional table satisfies ||H-H_hat||_1 < gamma/||w_full||_infinity, then every such table violates the same inequality. Here the infinity norm is the largest absolute table coefficient of the functional. Equality at the margin is insufficient for strict rejection. One can instead bound each table entry separately and sum coefficient-weighted radii. The conditional-probability confidence region must account for the division by q and must exclude q=0; alternatively multiply the inequality by q and work with the unnormalized branch. The frame, private-input interpretation, and communication architecture must themselves be justified; a table-space certificate alone does not establish them from logs.

A single positive fitted candidate gives no corresponding exact acceptance statement for every model in its confidence region. It supplies only the separately bounded approximation to the true process. Robust rejection needs the entire admissible confidence region to violate an inequality or otherwise be disjoint from the realization class.

An infeasible core at the canonical necessary messages means those ports need refinement or a different architecture; it does NOT mean no decomposition exists. Feasible message partitions need not have a unique least member. For the binary PR table, revealing x_1 but not x_2 is feasible: broadcast x_1, sample a fair lambda, set y_1=lambda and y_2=lambda XOR x_1 x_2. Revealing x_2 alone is likewise feasible, with y_2=lambda and y_1=lambda XOR x_1 x_2. The two outgoing-message vectors are incomparable; their common coarsening is constant messages on both sides and is infeasible. Thus the canonical profile quotient is a universal lower bound, but after its failure genuine architecture search can branch among incomparable port refinements.

## 4. Proper nonsimplicial retractions exist

Consider one local channel with X={0,1,2}, Y={0,1}. Let U be the subspace of equal-row-sum tables whose row 0 equals row 1, with row 2 unconstrained apart from having that same sum. Define P by replacing rows 0 and 1 with their average, leaving row 2 unchanged.

This P is linear, maps W to U, fixes U, preserves ell and entrywise nonnegativity. The space U has dimension 3. Its normalized positive base is a square: choose independently the probability of output 1 for the repeated first row and for the last row. Thus C has FOUR extremal rays, not three. The retraction class is not secretly limited to simplicial cones, and this is a proper subspace of the original W (which has dimension 4).

A nontrivial coupled example uses two such sites. Put e(0)=e(1)=0 and e(2)=1. Sample uniformly one of the four binary functions f:{0,1}→{0,1}, and output

    y_1=f(e(x_1)),   y_2=f(e(x_2)).

Both observable mode spaces equal the U above. To check the span, delete duplicate rows/columns and use the four-by-four matrix in Section 6.2 of the preceding note; it has rank 3 and row-sum relation (row00+row01)=(row10+row11). The fourth row is the sum of the first two minus the third, while the first three are independent. Therefore U has the claimed dimension. This H has a positive four-instruction realization and is accepted by the new LP, while the simplicial test does not apply.

For contrast, the duplicated-input PR channel, uniform on

    y_1 XOR y_2 = e(x_1)e(x_2),

has the same U and the same positive retractions, but its core LP is infeasible. Indeed every deterministic local strategy in a positive mixture would have to satisfy all four parity equations at the two effective input values; XOR of their left sides is 0 and XOR of their right sides is 1. This contradiction excludes every such strategy and hence every positive mixture. These examples are standard local-polytope phenomena, used only to verify that the new certificate both extends the first test and retains a real obstruction.

## 5. Temporal and data obligations remain unchanged

A separate retraction/core certificate is required for every used public transcript. The reconstructed local and core tables are fixed mechanisms, reused at each step; fresh shared innovations are allowed only where the type universe permits them. Matching transition kernels gives matching controlled path laws only from the SAME joint initial law. That joint law must itself have a separately admissible positive initialization protocol whose communication, shared randomness, and description costs are charged. This note is not an initialization theorem.

All incoming instruction alphabets, broadcast transcripts, and shared-core support/table sizes are charged. The all-ray LP can introduce many redundant local channels and an exponentially large core. Its existence does not establish a compact representation.

These are exact candidate-model certificates. Finite records do not establish exact subspaces, zero entries, or exact retractions without additional assumptions. A certified exact candidate may be compared against the true controlled process by the separate finite-basis total-variation bridge and its rank/coverage/confidence hypotheses. No physical local states or intervention access are thereby identified from passive logs alone.

## 6. What remains genuinely open

Without positive retractions, the all-ray restricted-span LP is not justified as a complete test for arbitrary positive local mechanisms. This note does not supply either a general reduction eliminating that gap or an explicit local-channel example separating the two classes. Such a counterexample or a wider completeness condition remains an independent question.

More importantly, the theorem works after a candidate operational frame and its port assignment have been reconstructed/proposed. It does not solve simultaneous unknown positive state-cone discovery, compatible factorization of alternative crossing frames, compact persistent shared-state discovery, or minimal stochastic/interactive communication.

At full W_i, the retractions are identities and the theorem is exactly finite local-polytope membership in a changed generator basis. Proper positive retracts give a checkable dimensional reduction with a completeness proof, but this is not by itself a new mathematical mechanism. The research burden remains combining such certificates with genuinely unknown spatial structure and restricted, compact interfaces inferred from readout behavior.
