# A temporal coupling invisible in every proper state view

## Plain-language abstract

Two three-mode mechanisms can be coupled by the direction in which they move around their modes. Every separate numerical summary which merges any two modes loses that directional coupling, even though the collection of state maps can distinguish all individual modes. Retaining the same transition identities across these views restores the missing correspondence and allows the coupling to be detected. The missing information is not a hidden state value: it is a relation between the state before a transition and the state afterward.

This example is a one-step dynamic obstruction, not a claim that all one-step tests succeed but a longer path fails. It refutes inference from independently factorizable proper state views to independence of the original transition system. It does not by itself provide a controller or a physically implemented repair.

## Exact finite plant

Let Z=Y={0,1,2}; the whole state set is X=Z×Y. For either component's ordered transition r=(z,z′), define L_r to be +1 on 0→1,1→2,2→0; −1 on 1→0,2→1,0→2; and zero on self-loops.

For each local transition pair r=(z,z′), c=(y,y′), define

    M_rc=1+L_r L_c.

The actual event carrier consists of triples (r,c,k), with 1≤k≤M_rc. Its source is (z,y), target is (z′,y′). There is one common action label. Distinct k are distinct transition records; they are not probabilities. If a hardware interpretation is desired, their distinct primitive execution routes must be supplied separately.

M has values 0,1,2. Oppositely oriented nontrivial transitions have multiplicity zero, equally oriented ones have multiplicity two, and pairs involving a self-loop have multiplicity one. Thus independence fails already at support level: a clockwise transition on the first mechanism and a counterclockwise transition on the second are each individually possible but cannot occur together. The state space itself is a genuine Cartesian product, so the obstruction is behavioral rather than a failure to factor snapshots.

For r+ and r− of opposite orientation, and likewise c+,c−, the corresponding 2×2 minor is

    [[2,0],[0,2]],

whose determinant is four. Hence there is no exact zero-signal independent transition factorization of this fixed state cut, even allowing arbitrary finite local nondeterminism and parallel records.

## Every proper state view passes the numerical factorization test

Choose proper state quotients p:Z→Zi and q:Y→Yi. The observation graph retains each actual event record but coarsens its endpoints by p×q. Its local transition-type aggregation maps are p×p and q×q. Every proper three-state quotient kills L. Thus the observed multiplicity matrix is exactly the outer product of the sizes of the transition-type fibres:

    Mbar_uv=|(p×p)⁻¹(u)| · |(q×q)⁻¹(v)|.

It has a finite exact independent event factorization after choosing endpointwise bijections. All 16 pairs of canonical proper state quotients pass. The nonconstant quotient family jointly separates every pair of original component states.

This conclusion is deliberately limited: independently chosen local event-factorization bijections are not asserted to satisfy every cross-view anchor of a global witnessed factorization. The full plant has no such global factorization. That distinction is precisely why numerical reflection and witness descent require separate criteria.

## What actual record alignment restores

The preceding failure concerns inference from independent numerical transition summaries. If the same actual event names are retained across the views, the proper quotients jointly distinguish every source state and every target state. For each event, the tuple of its viewed source labels uniquely determines its original source; likewise for its target. Thus aligned records reconstruct the entire original graph and detect the obstruction.

The independent checker verifies this reconstruction for all 81 actual records. It also verifies that each separate aggregate matrix equals the corresponding aggregate of the independent all-ones matrix. The two systems therefore have matching numerical summaries, and individually isomorphic coarsened event graphs after suitable per-view record relabellings, but those relabellings cannot be assembled into a single coherent endpoint-preserving identification of the whole systems.

This is not a counterexample to the value of witnessed views. It shows precisely why the witness correspondence carries information that independently summarized views discard.

## Relation to the general reflection criterion

The perturbation L⊗L is nonzero, has zero row and column sums, and is killed by all the permitted coarse observations. It is an explicit element of the aggregate-only invisible interaction space. The example realizes the failure direction of the general linear reflection theorem with N=1, retaining actual zeros so the failure is not merely an event-count effect.

The independent checker verifies the endpoint-safe construction, the nonzero minor, every proper-view rank test, and joint state separation. It does not assert this elementary circulation mechanism is historically new.
