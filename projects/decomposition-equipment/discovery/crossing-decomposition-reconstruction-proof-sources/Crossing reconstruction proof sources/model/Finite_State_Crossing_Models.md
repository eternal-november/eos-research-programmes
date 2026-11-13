# Finite state models for crossing reconstruction

## Plain language summary

Two individually workable ways of dividing a system need not be workable together. A subsystem may decode a boundary signal using state held inside it. After two divisions are combined, the smaller shared subsystem may no longer contain that decoding state. Even supplying both old boundary signals can then be insufficient. This is a genuine failure of the system's update rules to be determined by the available information, not a failure to intersect sets.

The first model below has four Boolean state coordinates and two fixed sensor signals. Two crossing divisions each work exactly. Their common refinement does not, even with both sensors. One additional raw sensor repairs the failure, with several different physical implementation choices. The second model gives failures of arbitrarily high order: every proper subfamily of proposed divisions can be jointly realized, while the entire family cannot under a fixed raw-sensor budget.

These are finite synchronous dynamical systems, not a completed virtual-equipment construction. Admissibility restrictions are predicates inside an ambient semantics; they are not claimed to be closed under every composition or interface change. The source supplies elementary proofs and exact finite checks. The separate abstract development is responsible for any equipment-level integration.

## 1 Ambient finite synchronous semantics

Let I be a finite set of named coordinates, let each X_i be a finite nonempty set, and put X=product_{i in I} X_i. A whole is a total deterministic update f:X→X. All states in X are admitted as initial states. This last convention matters: restricting to a reachable subset can remove distinctions used by the impossibility proofs.

For U⊆I write X_U=product_{i in U} X_i and f_U=projection_U∘f. An external observation for U is a function q:X_{I\U}→O. It is sufficient when there exists a local update

    g_U:X_U×O→X_U

such that g_U(x_U,q(x_{I\U}))=f_U(x) for every x∈X. Equivalently,

    ker(x↦(x_U,q(x_{I\U}))) ⊆ ker(f_U).

If q is surjective, g_U is unique. If not, its values on unreachable interface observations are irrelevant to realization; we identify implementations differing only there. Synchronizing these exact local updates for a partition of I recovers f, hence recovers every finite trajectory by induction. This is stronger than matching one observed run.

A physical sensor apparatus is a fixed list of functions s_j:X_{S_j}→O_j with declared coordinate supports S_j. A subsystem U may use sensor j as an external boundary sensor only if S_j∩U=∅. For a chosen permitted sensor set J, its boundary is q_J=(s_j)_{j∈J}. The policy may bound |J|, restrict sensor types, or prohibit particular combinations. An arbitrary function of unobserved coordinates is not automatically an available sensor.

A decomposition consists of a partition P of I and a sufficient permitted q_J for each block U∈P, together with its realized local update. A common refinement of several decompositions has a partition finer than all their partitions and must itself satisfy the physical sensor policy. For the examples we compare the partitions and their exact whole behavior, not equality of their original sensor lists; a finer block may use the available sensors afresh. Thus the obstruction is not manufactured by requiring identical old port lists.

The named-coordinate, surjective-sensor convention gives discrete realization choices. It does not manufacture nontrivial automorphisms. Nonisomorphic choices of physically different sensors are nevertheless genuinely distinct realizations. An abstract groupoid theorem must specialize correctly to these discrete fibers.

## 2 Crossing failure caused by lost decoding state

Take I={c,u,v,z}, all X_i={0,1}, and

    c'=u⊕v⊕z,  u'=u,  v'=v,  z'=z.

The only physical sensors initially available are

    a=v⊕z, with support {v,z};
    b=u⊕z, with support {u,z}.

There is no raw u, v, or z sensor. The fixed sensor outputs are allowed; arbitrary other preprocessing is not.

Consider the crossing partitions

    P={{c,u},{v,z}},
    Q={{c,v},{u,z}}.

P is realized: block {c,u} reads a and updates c'=u⊕a, u'=u; block {v,z} is autonomous. Q is realized: block {c,v} reads b and updates c'=v⊕b, v'=v; block {u,z} is autonomous. Each uses only a sensor whose support is outside the block.

Any partition finer than both P and Q is the singleton partition. The singleton {c} may read both a and b, but these are insufficient. The two states

    (c,u,v,z)=(0,0,0,0) and (0,1,1,1)

have the same local c and the same observations a=b=0, while their next c values are 0 and 1. No deterministic local update on (c,a,b) can realize the whole. The other three singleton blocks are autonomous. Therefore P and Q admit no admissible common refinement in this apparatus, even though both are individually realized exactly.

This failure is not an interface-capacity bound: the smaller subsystem already receives every available external sensor. Each parent previously held a different decoding key in its local state.

### 2.1 Exact equivalence relation calculation

Let p_P=(c,u,v⊕z), p_Q=(c,v,u⊕z). Their kernel relations R_P,R_Q respectively toggle the pairs (v,z) and (u,z). Their join in the lattice of equivalence relations is

    R_P∨R_Q = ker(c,u⊕v⊕z).

For fixed c each class has four states. At (u,v,z)=000 the class is {000,011,101,110}. The combined-boundary observation b_C=(c,v⊕z,u⊕z) instead has two-element kernel classes. Its class at 000 is {000,111}. Hence

    ker(b_C) is not contained in R_P∨R_Q.

This realizes the failure of the crossing information criterion in the abstract development. In particular, knowing separately that the update factors through both parent observations does not imply that it factors through the new local state and the combined parent boundary signals.

### 2.2 Repair and nonunique realizations

If the apparatus is enlarged by one raw sensor, any one of u, v, or z suffices:

    with u: c'=u⊕a;
    with v: c'=v⊕b;
    with z: c'=a⊕b⊕z.

Using no additional raw sensor is insufficient, as proved above, so one is the minimum number of additional raw sensors among these repairs. These are three distinct physical implementation options, not copies distinguished by an arbitrary label. The first two use two boundary signals total; the third uses three. A separate total-port budget can therefore distinguish their admissibility.

This is only minimality within the stated sensor-addition class. Adding a new computed sensor u⊕v⊕z would also solve the problem but is a different apparatus extension, not a free operation.

## 3 Raw wire factorization criterion

Suppose every external sensor is a raw coordinate projection. For each output coordinate i define its essential dependency set

    D_i={j∈I | there exist x,x' differing only at j with f_i(x)≠f_i(x')}.

For U⊆I put

    B(U)=(union_{i∈U} D_i)\U.

Proposition. A raw boundary S⊆I\U is sufficient for U iff B(U)⊆S.

Proof. If j∈B(U)\S, an essential-dependency witness changes only j, keeps all local coordinates and supplied sensors fixed, and changes at least one local output. Thus no local update exists. Conversely, suppose B(U)⊆S. Any two states agreeing on U∪S can be connected by changing their remaining coordinates one at a time. None of those coordinates is essential to any output in U, so f_U stays fixed throughout. Thus f_U factors through projection to U∪S. All coordinate sets are nonempty, so every local-and-boundary assignment occurs and the resulting update is unique. ∎

For a uniform budget k, a partition P is admissible iff |B(U)|≤k for every block U. This is computed from the actual update truth table, not posited from a graph of presumed dependencies.

For general f, inadmissibility of an intersection atom does NOT imply that every finer partition is inadmissible: splitting an atom can remove output coordinates and their dependencies. The exact common-refinement condition is that every nonempty intersection atom can be partitioned into feasible subsets U satisfying |B(U)|≤k. This is an exact finite-cover criterion, not a promised polynomial algorithm.

### 3.1 Crossing interface upper bound

For C=intersection_{t=1}^m U_t,

    B(C) ⊆ union_{t=1}^m B(U_t).

Indeed, an essential source for an output in C that lies outside C lies outside at least one U_t, hence belongs to that parent's external dependency set. Thus supplying the union of the parent raw boundaries always suffices for the intersection. The size bound is at most the sum of their sizes; duplicate raw sources need be supplied only once.

This property is special to raw projections (and other observation algebras satisfying the corresponding information condition). Section 2 proves it false for arbitrary fixed encoded sensors. That distinction is part of the crossing problem, not a notational choice.

## 4 Arbitrarily high order failure under bounded raw interfaces

For r≥2 let I={0,1}^r, n=2^r, X_i={0,1}, and

    f_i(x)=AND_{j≠i} x_j.

For every i, every j≠i is essential: set all other inputs to 1 and toggle j. The coordinate i itself is not essential. Consequently, for every nonempty U,

    B(U)=I\U,  |B(U)|=n−|U|.

Use raw-sensor budget k=n−2. For each t∈{1,...,r}, let P_t split I according to the t-th bit of its coordinate index. These partitions are fixed cuts of the same synchronous system.

For a subfamily S of s distinct cuts, its intersection atoms have size 2^{r−s}. If s≤r−1, this is at least 2, so the intersection partition itself is admissible: every block uses n−2^{r−s}≤n−2 raw sensors. Its exact local update is the restriction of f. Thus every proper subfamily has a genuine common refinement.

For the full family, all intersection atoms are singletons. Every common refinement must therefore be the singleton partition. Each singleton needs n−1 raw sensors, exceeding k=n−2. No admissible common refinement exists.

Theorem. For every r≥2 there is a finite synchronous system and r crossing decompositions such that every proper subfamily is jointly realizable but the full family is not.

This precludes a universal bounded-family-size test for joint realizability over this class as system size and budget vary. It does not prove complexity hardness, nor refute bounded checks under stronger structural assumptions or fixed system size. The obstruction comes from physically exposed state needed by the update, not an inconsistent parity-assignment CSP: all actual system states and transitions already exist.

### 4.1 A semantic abstraction with a nontrivial implementation problem

At an extensional interface level, permit observation functions as semantic interfaces. For any nonempty block U the one-bit function

    q_U(x_{I\U})=AND_{j∉U}x_j

is sufficient, with

    f_i(x)=q_U(x_{I\U}) AND (AND_{j∈U\{i}}x_j), for i∈U.

Thus every partition, including the full singleton refinement, has one-bit extensional interfaces. A concrete implementation of q_U consists of a set S of accessible raw sensors and a decoder δ such that q_U=δ∘projection_S. The denotation map forgets the implementation and retains q_U. Exactly n−|U| raw sensors are necessary and sufficient to implement q_U, because each outside coordinate is essential to the conjunction.

The semantic observation is therefore not itself an available physical wire. The proper families lift through denotation within budget; the full family does not. This separates abstract interface size from physical sensing requirements instead of merely erasing the update rules.

Composition of sensor implementations has the usual denotational substitution law. Fixed-cost admissibility need not be preserved by substitution: costs must be recomputed or tracked. No claim that the budget-bounded implementations form an equipment follows from this example.

## 5 Interface changes and surrounding contexts

### 5.1 Semantic reparametrization

If f_U(x_U,y)=g_U(x_U,q(y)) and an external adapter e:Z→X_{I\U} is supplied, then

    f_U(x_U,e(z))=g_U(x_U,q(e(z))).

Thus exact implementation transports along precomposition whenever the new interface policy permits q∘e. If e is surjective, an existing indistinguishability obstruction for q is preserved. For a non-surjective adapter, the obstructing pair may disappear, so failure need not persist.

Semantic transport alone does not preserve raw-sensor cost. An old one-bit raw observation y can become q∘e(z)=AND(z_1,...,z_m), requiring m raw sensors. Hence unrestricted adapter substitution and a fixed raw-port bound are not automatically compatible.

### 5.2 Refinement and grafting

If T⊆U, the raw boundary needed for T satisfies

    B(T) ⊆ (U\T) ∪ B(U).

The child can read formerly internal parent coordinates plus the parent's external boundary. This proves an explicit interface expansion bound for nested refinement. Exact composition of the corresponding local updates recovers f_T because all equations hold on the full state product. It does not assert that the child's expanded boundary meets the original k bound.

Replacing a surrounding component while preserving precisely the external observations q presented to U preserves U's realized local update. Replacing the whole with one whose update on U does not factor through q is outside that hypothesis. This source supplies a typed information-preservation statement, not a general controller-safety or behavioral-equivalence theorem.

## 6 Scope and baseline separation

The raw dependency criterion is elementary finite-function dependence analysis. The high-order family is an exact application showing why pairwise crossing checks cannot suffice uniformly under the stated physical policy. The encoded-sensor example exposes a different failure: combining sufficient parent interfaces need not yield a sufficient crossing interface, even without a capacity limit.

These facts are ingredients for, not a substitute for, the proposed abstract reconstruction theorem. The following still require separate proof: realization groupoids with nontrivial symmetries; compatibility with the chosen ambient equipment; a general local-to-global criterion for crossing families; and a comparison to established automata decomposition, contextuality, and descent results. No Lean verification, universal novelty claim, or practical robotics validation is asserted here.

## 7 Linear dynamics give an explicit obstruction and repair calculation

Let the finite coordinate sets be a finite field F and let the whole update be x'=Ax on F^I. Fix a crossing family of blocks U_t with C=intersection_t U_t. Let the allowed parent sensor rows form matrices L_t supported outside U_t. Write E_U for the row space spanned by coordinate projections in U, and write A_U for the rows of A with output indices in U.

A parent realization exists exactly when

    row(A_Ut) ⊆ P_t := E_Ut + row(L_t).

This follows because a linear update factors through the linear observation matrix iff its kernel contains the observation kernel, equivalently its row space is contained in the observation row space. Nonlinear decoders do not improve this criterion on the full vector space: constancy on observation fibers is still necessary, and implies the displayed linear factorization.

The proposed crossing observation consists of the retained local coordinates C and all parent sensors. Its row space is

    B := E_C + sum_t row(L_t).

The actual crossing-update obstruction is the vector space

    O_C := (B + row(A_C))/B.

Its dimension is computable as

    d_C = rank([B;A_C]) − rank(B),

where any matrix spanning B may be used in the stack. The crossing update is realizable exactly when d_C=0. The entire parent-information class transfers across this crossing exactly when

    intersection_t P_t ⊆ B.

Indeed, a linear output available from each parent is precisely a covector in intersection_t P_t. The same universal criterion holds for arbitrary finite-valued parent-computable functions in this full vector-space setting: the join of the kernels of the parent observations is the kernel annihilated by intersection_t P_t.

### 7.1 Minimum unrestricted linear repair

Allow additional scalar linear sensor measurements supported outside C. Exactly d_C additional independent measurements suffice, and fewer than d_C cannot suffice.

For sufficiency, choose d_C rows from A_C whose classes form a basis of O_C. Delete each row's coordinates in C; this changes it only by an element of E_C⊆B, so the quotient classes are unchanged. These exterior rows are legitimate new boundary measurements and eliminate O_C. Necessity follows because adjoining one scalar measurement increases the observation row-space dimension by at most one and can decrease d_C by at most one.

This is a sharp number of scalar channels only when arbitrary new linear measurements are permitted. With a fixed physical sensor catalog S={s_j}, the correct problem is to find a permitted subset J such that

    row(A_C) ⊆ B + span{s_j:j∈J}.

The smallest |J| can exceed d_C. For a local coordinate c with update c'=x_1+...+x_n in external coordinates, let B=span(e_c). Then d_C=1 but a catalog consisting only of the n raw external coordinate rows requires all n sensors. Thus abstract information dimension does not equal physical observation cost.

For the four-bit XOR example, C={c}, B=span(e_c,e_v+e_z,e_u+e_z), and A_C=e_u+e_v+e_z. The rank is 3 before and 4 after adding A_C, so d_C=1. Each of the raw rows e_u,e_v,e_z spans the same nonzero quotient class, giving the three different repairs previously described.

### 7.2 Transport of the actual obstruction

An external linear adapter y=Ez, with local C unchanged, induces pullback of covectors along diag(id_C,E). Transport both the update and its supplied sensor observations along this same adapter. The induced map gives a surjection from the old obstruction space onto the new one, so

    d_C(new) ≤ d_C(old).

If E is surjective, covector pullback is injective and equality holds. This proves preservation of success and identifies exactly why a restriction of possible environments may remove failure. It does not guarantee that the transported sensor rows belong to a new physical catalog or satisfy its cost bounds; those are independent admissibility obligations.

This linear theorem is a concrete calculable specialization, not a novelty claim about rank-nullity or observation factorization. Its contribution to the larger task is to make the crossing defect, interface repair, and transported obstruction explicit in actual finite-state dynamics rather than postulating that compatible descriptions glue.
