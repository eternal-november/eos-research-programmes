# Full unital replacement for the mandatory I2 mixed tests

The coordinated I5 proof is ../theory/Full_Unital_I5_Observation_Repair.txt, Sections 3 and 5. The argument is repeated here only to make the original I2 mandatory-test replacement self-contained; it is not claimed as a second independent theorem.

## Fixed language and monoid

Use the original transformation monoid M_k, k>=4, with t=k-1 and normal forms A_i, B_i, D_i from the unchanged monoid_repair_theorem.md. Write e=A_0, a=A_1, b=B_0 and b squared=D_0. The initial observation is H={e,b,b squared}. The specified cut language contains exhaustive joint ordered binary factorization, every generated finite cut tree, and the vertex-free unary unit test U(x), true exactly at e. Graft contexts include left and right multiplication. The following statements are on the actual nonempty unary identity old record, where every active cut is a path; old metadata and empty occurrences are retained. They do not infer a uniform product partition at branching ranks.

The old pair e,b is withdrawn because U already separates it. The replacement pair is b,b squared, both nonidentity elements.

## The exact full unital cut only partition

Let R have singleton blocks {A_i} for 0<=i<=t, paired blocks

    Z_i={B_i,D_i}        for 0<=i<=t-2,

and singleton blocks {B_(t-1)}, {B_t}. There are 2k blocks. This is the coarsest equivalence refining H membership and stable for binary cuts and U; hence it is equality of all finite Boolean cut-only theories on this unary slice.

**Upper bound.** Only the paired sources need checking. From the original complete multiplication table, for 0<=i<=t-2 the complete ordered factor-class signature of either B_i or D_i is

    {({A_0},Z_i)}
      union {(Z_j,{A_(i-j)}):0<=j<=i}
      union {(Z_0,Z_i)}.

Indeed a positive A-row left factor produces only A-row elements. A positive B/D-row left factor can produce B_i or D_i only with right factor A_l and indices adding to i. A zero-index B/D left factor produces the pair with right factor A_i or an element of Z_i, giving exactly the remaining pairs above. The two actual elements realize each listed pair by switching B and D choices as the table indicates. No constant or penultimate overflow can yield an index i<=t-2. Singleton source blocks need no comparison. The actual unit e is already singleton, so U is invariant. Source-fixed recursive matching of binary cuts, together with the zero-tree base, gives every generated unary tree and retained factor tuple. Thus R is cut-only stable.

**Lower bound by allowed formulas.** Put P=not H. For n>=1 let F_n mean that there is an n-factor ordered factorization with every factor in P (F_1 is P). A nonconstant of index i<t has F_n exactly for 1<=n<=i; either constant has F_n for every n. The table proves the upper bound on n by additive indices for a nonconstant product. The lower bound uses A_i=a^i, B_i=B_1 a^(i-1), and D_i=D_1 a^(i-1) for positive indices, merging adjacent positive factors as needed. Constants may be followed by arbitrarily many a factors without changing. Thus finite generated predicates F_n distinguish every different index, including a finite index from the constant index.

Let V=H and not U, and define the allowed cut-only formula

    chi_a = P and not <binary>(P,P) and not <binary>(V,true).

The first two terms select exactly A_1,B_1,D_1. The last term rejects B_1 and D_1, since b a=B_1 and b squared a=D_1. It retains A_1: the table has no factorization of A_1 with left factor b or b squared when t>=3. Hence chi_a defines the singleton {a} uniformly for every k>=4.

Now let

    T = <binary>(chi_a,true).

This holds exactly on the positive A-row elements A_1,...,A_t: each is a times A_(i-1), while every product with left factor a lies in that row. At index zero, U separates e from Z_0. At each positive index, T separates the A element from the B/D pair or the terminal B singleton. The index predicates, U and T therefore distinguish every R block. Combined with the upper bound, this proves the exact cut-only quotient rather than merely exhibiting some stable refinement.

The standard finite-image formula argument, or the explicit upper/lower construction just given, establishes adequacy for arbitrary cut nesting. No bounded-depth empirical inference is used.

## Adequate without contexts but not compositional

Use the explicit diagnostic observation q_R(x)=[x]_R. It is adequate for all predeclared cut-only formulas generated from H, including U, by the exact theorem above. But b and b squared have the same R class, whereas right multiplication by ab=A_t gives

    b(ab)=B_t,       b squared(ab)=A_t,

which are different R classes. Consequently right_ab is not a well-defined operation on this cut-only observable quotient. This supplies the mandatory observation-adequate-without-contexts but not compositional example without reusing the unit-separated e,b pair.

## A cut after a graft when neither unmixed language separates

The same b and b squared agree in every cut-only experiment by the exact R theorem. They also agree in every graft-only H experiment: H is a submonoid with ideal complement, so H membership is a multiplication congruence, and both original labels lie in H.

Apply the graft context right_ab. The resulting labels are B_t and A_t. Then apply the allowed cut-only test T. It is false at B_t and true at A_t. Thus the mixed formula

    right_ab^*(<binary>(chi_a,true))

separates the pair. This is literally a cut test following a graft and uses only the predeclared language. Neither its full cut-only sublanguage nor its full graft-only sublanguage separates the original pair. It does not claim this is the unique separating mixed formula.

For the two-channel family use (b,e) and (b squared,e), graft on the right by (ab,e), and use first-channel predicates. Pure cut equivalence follows from the cut-stable relation R on the first component times exact equality on the second; full joint factorization relations factor between the two independent monoid coordinates, and the actual pair-unit predicate is constant on these classes. Pure graft observations, also allowing channel swap, agree because the two H-membership channel vectors agree and the product H-observation is a multiplication congruence. The mixed formula acts in the first channel as above. This is a unary test embedded in the full graph-linked family, not a claim that its cut-only quotient determines all branching profiles.

## Relation to the corrected realization

These two controls replace the invalid examples in original I2 Sections 11.1 and 11.2. The companion rank-sensitive group realization supplies the independent nonidentity decoder and proper full-profile compression; its growing palette family supplies a strict minimum-state growth family. Repeated and empty occurrences continue to be handled occurrencewise in the full-profile realization proof, with the zero-tree case explicitly separate from nullary vertices. The M_k transformation table and its unchanged lower-bound proof remain the source for its larger simultaneous endpoint; any new full-unital elementary stabilization counts belong to the separate I5 repair, not to the old binary-only formula.
