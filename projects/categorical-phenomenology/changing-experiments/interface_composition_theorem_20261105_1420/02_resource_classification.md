# A sharp resource-matrix classification

Let m,d≥1 and fix n≥2. The resource category N^m has one arrow r→s iff r≤s coordinatewise. Its tensor is addition and unit is 0. A matrix C∈N^(d×m) gives a strict symmetric monoidal functor r↦Cr into N^d. No inverse or divisibility is assumed; resource units are indivisible.

For covariant diagrams X_i:N^d→Set, define additive-budget convolution

    (⋆_i X_i)(s) = colim_{s_1+⋯+s_n≤s} ∏_i X_i(s_i).

The indexing category has componentwise-order arrows. The canonical comparison is

    ⋆_i(X_i∘C)(r) → (⋆_i X_i)(Cr).

For Bool replace the colimit by OR and products by AND. For category-valued witnesses retain the Grothendieck category over the same decomposition poset, instead of taking a Set-colimit.

## The classification

1. Universal Bool exactness holds iff each column of C is either zero or one standard basis vector.
2. Universal Set exactness holds iff, in addition, no two nonzero columns have the same row: C is a partial coordinate injection, permitting zero columns.
3. Universal equivalence of retained Grothendieck witness categories holds iff C is a coordinate injection: the condition in 2 and no zero columns.

All quantifiers are over every budget r and every family of diagrams of the indicated variance. Fixed applications can satisfy exactness under weaker hypotheses. The theorem classifies the universal guarantee.

## Proof of 1

Fix physical demands b_i with ∑b_i≤Cr. The relevant lifting poset consists of allocations a_i satisfying ∑a_i≤r and b_i≤Ca_i. Bool exactness requires it be nonempty, by the general theorem specialized to thin categories.

Necessity: if a column c=C e_j has total coordinate sum ≥2, split it as c=p+q with p,q nonzero. Set r=e_j, b_1=p,b_2=q, and other b_i=0. A source allocation has ∑a_i≤e_j. Thus at most one a_i is nonzero; it is e_j if nonzero. Since both b_1,b_2 are nonzero, both a_1,a_2 must be nonzero, impossible. A nonnegative integer vector of total size at most1 is precisely zero or a basis vector.

Sufficiency: assume every column is zero or a basis vector. For each output coordinate ℓ, the source resource coordinates J_ℓ={j:C e_j=e_ℓ} have total supply ∑_(j∈J_ℓ)r_j. The inequality ∑_i b_(i,ℓ)≤∑_(j∈J_ℓ)r_j permits distributing those integer units among n bins of prescribed demands b_(i,ℓ). A greedy fill constructs nonnegative integers a_(i,j) with ∑_i a_(i,j)≤r_j and ∑_(j∈J_ℓ)a_(i,j)=b_(i,ℓ). Set allocations in zero columns to0. These allocations satisfy the lift conditions, proving existence. This is actual resource allocation, not a choice separately dependent on a hidden world.

## Proof of 2

Necessity of the column condition follows from the same empty-lift obstruction. If two columns j≠k equal e_ℓ, set r=e_j+e_k and physical demands b_1=b_2=e_ℓ (other b_i=0). A lift must give one whole distinct source unit to each of components1,2. There are exactly two lifts: (a_1=e_j,a_2=e_k) and (a_1=e_k,a_2=e_j). There is no arrow between them, and no other allocations can connect them because all supply is already used. The lift category is discrete with two objects. For threshold representables X_1(s)=N^d(e_ℓ,s), X_2(s)=N^d(e_ℓ,s), and X_i(s)=N^d(0,s) for i>2, the source convolution has two elements and the target convolution one. Thus Set exactness fails despite universal Bool exactness.

Sufficiency: if C is a partial coordinate injection, each supported physical coordinate ℓ has a unique source coordinate j with C e_j=e_ℓ. Given demands b_i with ∑b_i≤Cr, define a_i^min at that j to be b_(i,ℓ) and set every zero-column coordinate to0. The demands in rows not in the image are zero. The tuple a_i^min is feasible, and every lift a_i satisfies a_i^min≤a_i componentwise. Thus the lifting poset has a least object. It is nonempty and connected (indeed its nerve is contractible), and the general Set theorem proves exactness.

## Proof of 3

Universal witness equivalence requires the decomposition functor K_r be an equivalence, hence final; therefore the Set criterion is necessary. If C has a zero column j, set r=e_j. The physical decomposition category at Cr=0 is terminal. The source decomposition category contains the all-zero allocation and the distinct allocation with e_j at component1, with a noninvertible arrow from the former to the latter. It is a poset with at least two nonisomorphic objects, so cannot be equivalent to the terminal category. Thus zero columns are forbidden.

Conversely, if the columns are distinct basis vectors, every decomposition b_i with ∑b_i≤Cr has a unique inverse allocation a_i obtained by reading its supported coordinates; all unsupported coordinates of b_i are forced zero. This inverse preserves and reflects componentwise order. Hence K_r is a poset isomorphism. The total witness-category comparison is therefore an isomorphism (up to chosen product conventions), in particular an equivalence, for all category-valued diagrams.

## Three concrete, independent failures

- C=[2], r=1: two experiments each needing one physical micro-unit can be composed under physical budget2. Changing each interface first makes each component require a whole source packet; two components need two packets. The factorization category for demands (1,1) is empty. Example: one sealed packet contains two calibration reagents, and the changed local interface does not permit splitting a packet between distinct components. Global opening/sharing is an extra admitted decomposition, not free local copying.
- C=[1 1], r=(1,1): two labelled stocks are forgotten to one reagent type. Each of two one-unit experiments can receive either stock, creating two disconnected allocations. Feasibility is unchanged, but allocation provenance is not. A Set convolution that remembers elements of this colimit has cardinality2 rather than1.
- C=[1 0], r=(0,1): an audit token is invisible to the physical-budget translation. Source allocations form a span (0,0)→(1,0), (0,0)→(0,1) in the audit coordinate for n=2, while target decompositions are terminal. All factorization categories have least objects, so all Set comparisons are exact. Nonetheless the audit extensions remain noninvertible witness arrows, and their category is not equivalent to the terminal one. This is an especially simple final-but-not-equivalence example.

A positive nontrivial Set-exact map is C(q,audit)=(q,0), translating two source coordinates to a two-coordinate target interface, forgetting audit and admitting no units of the target's second resource. A positive witness-exact map is C(q)=(q,0): it genuinely changes the budget vocabulary while every admitted decomposition of an image budget lifts uniquely.

## Exact comparison with the prior manufacture result

The prior adaptive-manufacture theorem compares ∨_h C d_h with C(∨_h d_h) and requires each row of C to have at most one nonzero entry. It permits arbitrary positive integer weights and permits one source product to consume several physical resource types. The present convolution criterion instead asks whether bounded resource decompositions lift and connect. C=[2] satisfies the old row-support condition but fails even Bool convolution exactness. C=[1 1] fails the old join criterion but satisfies the new Bool criterion. Thus neither criterion is a renaming of the other; they classify different interchanges. The Set criterion is strictly narrower than both in the indicated directions and the witness criterion narrower still.
