# Observable channel cones and minimal deterministic outgoing ports

Status: exact constructive sufficient-class theorem, with a proved port lower bound. The positive Tucker/simplicial-cone mechanism is classical; this is not a claim that the general selected discovery target is finished or that priority is established. The theorem discovers local stochastic kernels and their correlated coupling from a learned transition law after a candidate operational coordinate frame has been inferred. The preceding calibrated reset-frame note supplies one way to infer that frame from recorded operations, rather than receiving subsystem boundaries as input.

## 1. Declared architecture and causal scope

Fix a public context v, which may include the current shared boundary state and a genuinely public command. Component i has a private input x_i in a nonempty finite set X_i(v). Empty/unreachable public contexts are omitted. This input includes its current operational state AND its private command when that command may influence an outgoing message. The allowed source inputs form the full product of these sets. Restricted joint input availability needs a separate support-indexed treatment and is not silently filled in.

The assignment of recorded command labels to public/private ports is part of the proposed certificate. It must preserve the actual command availability and causal access; inventing a Cartesian product of unrecorded or forbidden commands is not permitted. The full-product case below applies only when that input structure is justified by the declared universe and covered readout semantics.

The learned row-stochastic kernel is

    K_v(b,y_1,...,y_m | x_1,...,x_m),

where b is a shared next-boundary/public-output record and y_i is component i's next local state/output. The target alphabet Y_i(b,v) may depend on the next boundary and is nonempty for every used branch q(b)>0. All this is the candidate operational realization learned from readout behavior, not asserted to be the unique physical latent state space.

The permitted protocol is a single deterministic-message round followed by correlated randomness:

1. Component i sends m_i(x_i) through a declared outgoing port.
2. A shared interface sees only v and the message tuple m. It samples b and a tuple of random local instructions r=(r_1,...,r_m).
3. Each component sees the declared public transcript (v,m,b), its local instruction r_i, and its own x_i, and samples y_i using one fixed local kernel table.

This protocol does NOT grant the interface access to private inputs or commands beyond their messages. Broadcasting the message tuple and b, and delivering r_i, are real type requirements with counted capacities. If that communication is prohibited by the chosen universe, this construction is not admissible. Analysis-only variables do not become controller observations.

The same local tables and shared sampling rule are reused through time. The random instructions may be freshly sampled in each transition; persistent physical parameters must instead be present in the carried state/boundary, not resampled between steps.

## 2. Discover the least deterministic information that must leave each component

For fixed v, define x_i equivalent_i x_i' if, for every other input x_-i and every shared/outside output (b,y_-i),

    sum_(y_i) K_v(b,y_i,y_-i | x_i,x_-i)
      = sum_(y_i) K_v(b,y_i,y_-i | x_i',x_-i).

This is equality of complete outside-response profiles, hence an equivalence relation. Let M_i(v) be its quotient and let m_i be the class map.

### Necessary minimality theorem

In ANY realization of the declared protocol with deterministic outgoing messages, its message partition for component i refines M_i(v). Thus it cannot use fewer message classes than M_i(v), and it cannot identify any pair that the displayed relation separates.

Proof. If two private inputs send the same message, the shared interface receives exactly the same transcript when all other inputs are fixed. Its distribution of b and all random instructions is therefore the same. Every outside component also has the same private input and the same received transcript. Consequently the joint outside-output law is unchanged. QED.

The quantifier is over deterministic encoders fixed independently of the shared random seed. A stochastic encoder can convey a continuously varying probability through a small alphabet; the theorem is NOT a lower bound on arbitrary stochastic or interactive communication.

## 3. Minimal messages make each message cell non-signalling

For a message tuple m, the private input cell is the product of the classes X_i(v,m_i). Write

    q_(v,m)(b) = sum_y K_v(b,y|x).

This is independent of the representative x in the cell: the equivalence condition preserves b's marginal when any one coordinate is changed, so change coordinates one at a time.

For b with q_(v,m)(b)>0 define

    H_(v,m,b)(y|x) = K_v(b,y|x) / q_(v,m)(b).

Then for each i its outside marginal sum_(y_i) H(y|x) is independent of x_i within that cell. Thus H is a non-signalling channel from the residual private inputs to the local outputs. This includes PRIVATE COMMANDS in the no-signalling test whenever they remain uncommunicated.

If q_(v,m)(b)=0, the entire b-row is unused for every input in the cell. No conditional H or fitted local table is needed on that unreachable branch. Arbitrary filling is harmless only because the shared sampling rule never takes it; this does not authorize arbitrary filling of partly observed or positive rows.

Non-signalling alone is insufficient for a local stochastic realization. The next condition is substantive.

## 4. Intrinsic positive channel-cone test

Fix a used triple (v,m,b), and abbreviate H=H_(v,m,b). Regard H as a nonnegative tensor with local mode i indexed by the pair (x_i,y_i). Let U_i be the real column space of its mode-i unfolding: the span of all local table vectors obtained by fixing the other input/output pairs. This space is computed from H; no local channel generators are provided.

Non-signalling implies that every vector L in U_i has a row sum independent of x_i. Let ell_i(L) denote this common row sum. Set

    C_i = U_i intersect {entrywise nonnegative local tables}.

The cone C_i is pointed, polyhedral and spans U_i. For every nonzero L in C_i, ell_i(L)>0. Assume C_i is simplicial: if r_i=dim U_i, it has exactly r_i linearly independent extreme rays.

Normalize these rays by ell_i=1, obtaining row-stochastic local kernels

    L_i,1,...,L_i,r_i.

These kernels are DISCOVERED from the observable section cone. Their labels need not be physical hidden-state identities.

### Positive simultaneous-realization theorem

Under these conditions there is a unique nonnegative coefficient tensor G on the local instruction tuple r such that

    H(y|x) = sum_r G(r) product_i L_i,r_i(y_i|x_i).

Moreover sum_r G(r)=1. Therefore G is a genuine joint distribution of correlated local instructions, independent of the residual private inputs x. Combining it with q_(v,m)(b) gives a realization of K_v by the declared deterministic-message/shared-randomness protocol. It attains the minimal deterministic outgoing message partitions M_i(v).

### Proof

Let A_i have the normalized extreme-ray vectors as columns. Since C_i is simplicial and spans U_i, A_i is a basis matrix and its coordinate inverse B_i on U_i sends every vector in C_i to a nonnegative coordinate vector.

Apply B_1 along the first tensor mode. Every first-mode fiber of H lies in C_1, so all resulting entries are nonnegative. Every fiber in another mode j remains a linear combination of the original mode-j fibers, hence remains in U_j. Since it is also entrywise nonnegative, it lies in C_j. Apply B_2, and continue. The final tensor G is nonnegative. Reversing the basis changes reconstructs H, and basis uniqueness makes G unique. Operations on different modes commute, so the resulting G does not depend on the unmixing order.

For any fixed private input tuple x, sum the reconstructed equation over y. Every L_i,r_i has row sum one; H also has row sum one. Hence sum_r G(r)=1. The coefficient tensor was obtained by a single multilinear basis change with x_i included in the mode, so it is not secretly a different random distribution for each private input. QED.

The proof is a finite version of simplicial-cone tensor nuclearity/positive Tucker unmixing. It is not new merely because it is written in port language.

## 5. Temporal reuse and actual correlated dynamics

Apply the construction to every allowed public context and message/boundary triple. The complete local kernel is one table L_i(v,m,b,r_i; y_i|x_i), and the shared table is q_(v,m)(b)G_(v,m,b)(r). These are fixed before an execution.

If x_i includes the current local state and y_i its next state, and b carries the next shared boundary, the rowwise identity with K implies equality of every finite controlled trajectory by induction PROVIDED both executions start from the same joint initial law. That joint initialization must itself have a separately admissible positive preparation in the declared interface universe, with its shared randomness, communications, and description costs counted. Merely retaining an arbitrary correlated initial law as a mathematical measure does not certify an implementable initialization. The theorem proves a transition realization, and becomes an initialized-process realization only after that preparation obligation is met. Local kernels are explicitly nonnegative and row stochastic on their source/target state fibers; no unproved positivity of a signed predictive operator on unreachable states is used.

This is genuinely correlated dynamics: G need not be a product law, and its distribution may depend on communicated state information. It is not Daduna's unconditional product transition law. But a global transition law must already have been operationally estimated/certified; the theorem does not turn arbitrary empirical correlations into causal intervention kernels.

## 6. Exact limits and counterexamples

### 6.1 Non-signalling can fail positive local realization

The binary PR relation, uniform on y_1 XOR y_2=x_1 x_2, has constant outside marginals, so the minimal messages are both constant. It has no local shared-randomness realization with no transmitted private inputs. Its local channel section cone is non-simplicial. This is a standard contextuality/Bell example, not the theorem's new achievement.

### 6.2 Non-simpliciality is NOT a general impossibility certificate

Choose a random binary function f:{0,1}->{0,1} uniformly from the four possibilities, and let both components output y_i=f(x_i). This is an explicit local shared-randomness realization with no outgoing messages. Its flattening by (x_1,y_1) versus (x_2,y_2) is

    [1/2, 0,   1/4, 1/4]
    [0,   1/2, 1/4, 1/4]
    [1/4, 1/4, 1/2, 0  ]
    [1/4, 1/4, 0,   1/2].

Its local span is the three-dimensional space of binary channel tables with equal row sums. The positive section cone has FOUR extreme rays, the four deterministic binary functions. Therefore the simplicial test fails even though the displayed four-instruction realization exists.

A failed cone test says only that this canonical rank-tight extraction is unavailable. It does not establish nonexistence of a positive factorization, or the necessity of transmitting more information. Larger/redundant local generator families may work.

### 6.3 Counts and hidden costs

Outgoing port sizes are |M_i(v)|. Incoming instructions have sizes r_i, and the shared distribution can have support as large as product_i r_i. The public transcript can have product_i |M_i(v)| possibilities. All these sizes, the table/circuit description of G, and the broadcast of m and b must be counted. A huge shared core is not a compact discovery result.

Extreme-ray enumeration and repeated inference over candidate frames/message types may be expensive. The theorem is a constructive sufficient criterion, not an assertion of a polynomial-time general factorization algorithm.

### 6.4 Data versus exact model claims

Exact profile equality and simplicial cone identities are properties of the candidate ideal operator model. Finite samples alone do not establish them without a separation/discrete-model promise. A statistically valid route is to construct an exact positive candidate assembly inside a simultaneous confidence family and compare its controlled law with the true rank-bounded law using the finite observable-basis error theorem. That comparison requires BOTH the true law and candidate assembly to satisfy the declared observable-rank bound, or an exact candidate intertwining into the certified rank-r realization, together with the stated common-basis conditioning and coverage hypotheses. Finite-table agreement with a higher-rank candidate is insufficient. Then the assembly is an APPROXIMATE operational decomposition with the resulting risk budget. Its minimal ports are minimal for that candidate and protocol, not proven exactly minimal for the unknown physical environment.

Exact support, zero-risk safety and arbitrary intervention claims need additional assumptions. No controller gains access to internal analysis interfaces solely because a mathematical factorization uses them.

## 7. Why this is not the full selected target

This theorem gives an intrinsic, computable sufficient condition which constructs both local kernels and a joint positive coupling, and attains a justified deterministic port lower bound. It is stronger than fitting local models separately or merely asserting the existence of a cone diagram.

It does not discover general nonsimplicial local positive realizations, jointly factor arbitrary alternative crossing frames, minimize stochastic/interactive interface capacity, or guarantee a compact shared core. The calibrated reset-frame route can also require a globally large observable representation. These are remaining substantive problems, not routine omissions.

Nearest mathematical foundations include nonnegative Tucker decomposition and the geometry of simplicial cones. For example Cohen et al., Some Theory on Non-negative Tucker Decomposition, studies the cones needed for modewise nonnegative reductions; its abstract specifically warns that preserving a nonnegative core can require many extreme rays. Source: https://orbi.umons.ac.be/bitstream/20.500.12907/41919/1/LVAICACohen.pdf . Exact theorem-level priority comparison has not yet been completed.
