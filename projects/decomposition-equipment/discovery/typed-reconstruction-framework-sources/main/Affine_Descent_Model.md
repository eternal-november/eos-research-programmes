# Unit-affine path calculus: a positive, non-graph model

## Plain-language abstract
This model permits arbitrarily many interacting inputs, not merely a fixed tiny example. A mechanism adds weighted inputs and an offset on a finite cyclic state space; every weight is reversible. Different observers retain different modular measurements of the same mechanism. Compatible measurements reconstruct an entire mechanism, including its possible factorizations, while retaining the ambiguity that observations leave unresolved. The chosen normalization does not preserve insertion of a new identity root; this model does not supply a unital 2-Segal result. A proposed factorization with a fixed outer mechanism and a specified actual whole can be lifted, not just its endpoint labels. Canonical cuts remain coherent after coordinate changes only when one also changes the coordinate on the newly exposed internal boundary. That internal change is derived explicitly below.

This is a calibration model for the general framework, not an architecture-discovery theorem, not a novelty claim for affine algebra or CRT, and not a discharge of the original graph-calculus contract. Reversible coefficients, positive arities, modular views and invertible affine coordinate changes are substantive scope restrictions.

## 1. Typed operations and substitution
Fix N>=2 and R=Z/N. Choose any set of interface names. There is one component color (A,B) per ordered interface pair. A path profile consists of colors (A0,A1),...,(A[n-1],An), with output (A0,An). For every such profile of length n>0 let its operation set be

    Aff_R(n) = {(b;a1,...,an): b in R, each ai in R^×}.

Its interpretation is f(x)=b+sum ai xi. Profiles, leaf occurrences and order are part of the data and never forgotten by a view. Substitution requires matching component colors and concatenates ordered profiles. If f=(b;Ai) and gi=(ci;dij), then

    f[g1,...,gm]=(b+sum Ai ci; (Ai dij) in lexicographic order).

Units are closed under multiplication. Associativity follows by expanding both constants and coefficients; the unary identity is (0;1). This gives a positive-arity typed multicategory for every N and every interface set. Arity is unbounded. There are no nullary factors and no implicit symmetric permutations.

## 2. An actual presentation, not an assumed quotient
For each composable pair use binary addition; for each component color use unary S_a(x)=a x for a unit and T_b(x)=x+b. Take the following typed equation schemes (all displayed terms must have matching path profiles):

* associativity of addition;
* S_1=id and S_a S_c=S_ac;
* T_0=id and T_b T_c=T_(b+c);
* S_a T_b=T_(ab) S_a;
* S_a(x+y)=S_a x+S_a y;
* (T_b x)+y=T_b(x+y) and x+(T_b y)=T_b(x+y).

Every term is equal under these equations to

    T_b(S_a1 x1 + (S_a2 x2 + ... + S_an xn)),

with the evident unary convention. Proof is structural induction. Unary translation adds to the outer translation; scaling distributes over the ordered sum and multiplies its coefficients and translation; addition moves both child translations to the root, concatenates the sums and reassociates. All coefficients stay units. Evaluation at the zero vector determines b, and evaluation at each standard basis vector then determines ai. Thus two normal forms denote the same function iff their parameters agree. This proves soundness and completeness of the presentation, without claiming a particular rewriting orientation terminates or is confluent. For fixed finite N there are finitely many parameter values and finitely many schemes; interface indexing is a typed schema. Across varying N this is a uniform effective family, not one fixed finite signature.

## 3. Canonical cuts and tree coherence
For a nonempty consecutive interval I beginning at i define its normalized inner factor

    h_I=(0; (a_j/a_i) for j in I).

Replace that interval in the outer operation by one input of coefficient ai, keeping all other coefficients and the original constant b. The composite is f. The inner factor has leading coefficient 1 and constant 0.

For any planar rooted positive-arity tree with this ordered leaf profile there is a canonical factorization: the root carries constant b; every other vertex carries constant 0. Write a_first(U) for the original coefficient of the first leaf below subtree U. A root edge to U has coefficient a_first(U); a nonroot edge from T to U has coefficient a_first(U)/a_first(T). Singleton leaf cases use the same rule. Products along paths telescope to the original leaf coefficient. Every nonroot factor has leading coefficient 1. Conversely these normalization conditions and the whole coefficients force all these edge coefficients. Consequently all nested and disjoint cut sequences yielding the same planar tree agree exactly. Nonroot unary vertices are identities. A unary root instead carries (b;a_first), so inserting a new root and renormalizing does not insert an identity unless b=0 and a_first=1. Accordingly this normalization is not asserted to commute with all operadic degeneracy insertions. A full-interval cut has this generally nonidentity unary outer factor.

This is chosen normalized-cut coherence. It is NOT uniqueness of arbitrary affine factorizations, an invertible full factorization map, or a claim that the full decomposition nerve is 2-Segal. Arbitrary factors admit internal affine gauge changes and redistribution of constants. Crossing row/column factorizations with different leaf orders are not equated: a reordering would require separately declared structure absent here.

## 4. Coordinate transport and the required internal gauge
Apply input coordinate maps r_j(x)=u_j x+v_j and output map r_0(z)=u_0 z+v_0, all u units. The transported whole r_0 f(r_1,...,r_n) has

    a'_j=u_0 a_j u_j,
    b'=u_0(b+sum a_j v_j)+v_0.

For I beginning at i put

    c_I=sum_(j in I) (a_j/a_i) v_j,
    t_I(z)=u_i z+c_I.

If h'_I denotes the normalized cut of the transported whole, direct coefficient calculation gives

    h_I(r_j:j in I)=t_I h'_I.

Transport the old outer factor by r_0, by r_j on inputs outside I, and by t_I on its collapsed input. It is exactly the new normalized outer factor. Thus cut/transport commutes with a DERIVED invertible internal coordinate map, not with an unchanged internal coordinate.

For sequential input changes r_j followed by s_j(x)=w_j x+z_j (so original inputs receive r_j(s_j(x))), the first normalized inner coefficients are a_j u_j/(a_i u_i). Its induced second gauge is w_i z+sum (a_j u_j/(a_i u_i))z_j. Composing it with t_I gives slope u_i w_i and translation sum (a_j/a_i)(u_j z_j+v_j), exactly the gauge induced by the composite input changes. This proves the transport cocycle. Nested tree transport follows by applying this identity at each vertex; uniqueness of normalized tree factors proves agreement with direct whole transport. Output changes cancel from inner coefficient ratios. Residue maps preserve these formulas and inverses of units, so the same mixed equations hold simultaneously in every view.

## 5. Modular views and hereditary reconstruction
Choose divisors d1,...,dk of N, each >=2. The view modulo di reduces every coefficient and constant, retaining its full typed profile. It is a surjective substitution homomorphism. Surjectivity on unit coefficients deserves proof: a unit modulo a divisor d lifts to a unit modulo N by lifting at primes dividing d and choosing a nonzero residue at primes dividing N but not d, then using prime-power CRT.

An overlap modulus equal to1 is interpreted as the terminal operation fiber on the retained profile (one parameter tuple); no nontrivial algebraic assertion about an excluded ring is needed. Two views agree on overlap precisely when their corresponding parameters agree modulo gcd(di,dj). Let L=lcm(di). Generalized integer CRT says pairwise-compatible parameter residues give a unique parameter modulo L. A compatible tuple of unit residues yields a unit modulo L, because every prime dividing L divides some di. The preceding unit-lifting argument then gives coefficients in R^×; constants lift ordinarily. Hence the compatible-view operation set is canonically isomorphic to Aff_(Z/L)(n), and

    Aff_R(n) / (equality modulo L) ≅ compatible view tuples.

This is true for every subfamily, profile and arity, and respects substitution, chosen cuts and the declared transports. The map to actual R-operations has fibers of size

    (N/L) * (phi(N)/phi(L))^n.

Thus reconstruction is unique only when L=N; otherwise these actual witnesses must be retained, not conflated with a canonical chosen lift. This is a full profilewise CRT application; CRT and the presentation normal form are standard ingredients, not asserted new mechanisms.

### The overlaps are actual congruence joins
Write E_d for profilewise parameter equality modulo d. Its intersection with E_e is E_lcm(d,e), since simultaneous divisibility by d and e is divisibility by their least common multiple. Its relational composite and congruence join are both E_gcd(d,e). Indeed E_d;E_e is contained in E_gcd(d,e). Conversely, for operations x,y equal modulo gcd(d,e), choose an intermediate parameter z equal to x modulo d and y modulo e by generalized CRT. For each coefficient, the prescribed residues are units, so their CRT class is a unit modulo lcm(d,e) and lifts to a unit modulo N. Constants use ordinary CRT. These choices give an intermediate operation z on the SAME full profile, with x E_d z E_e y. Hence E_d;E_e=E_gcd(d,e); as this is an equivalence relation containing both congruences it is their join. Thus the overlap objects used above are precisely the joins in the abstract descent theorem, not externally selected comparison targets. Together with intersections E_lcm and generalized CRT for every subfamily, this verifies the theorem's actual congruence hypotheses.

Example: N=120 with views 12,20,30 has overlaps 4,6,10 and L=60. Every compatible ternary operation has 2*2^3=16 actual witnesses. The same views at N=60 are separating. Arbitrarily many compatible modular views and arbitrarily long profiles are permitted.

## 6. Actual fixed-outer refinement lifting
This is stronger than lifting operation objects. Fix an ACTUAL outer f=(b;A1,...,Am), an ACTUAL target F=(B;(Bij)) with an ordered partition of its positive-arity leaves into m positive blocks, and a forest class modulo L represented by gi=(ci;dij). Suppose the quotient substitution equation holds:

    Bij ≡ Ai dij (mod L),
    B ≡ b+sum Ai ci (mod L).

Set d'ij=Ai^(-1) Bij in R. These are units in the prescribed residue classes. For i>1 choose any c'i≡ci modulo L and set

    c'1=A1^(-1)(B-b-sum_(i>1) Ai c'i).

The quotient equation proves c'1≡c1 modulo L. Then the ACTUAL forest g'i=(c'i;d'ij) lies in the specified whole forest class and satisfies f[g'1,...,g'm]=F exactly. This proves class-image saturation for every fixed outer operation and every positive block profile. The proof chooses a JOINT forest; no unsupported independent slot choices are used. Its arrow witness fiber has exactly (N/L)^(m-1) members: coefficients are forced; m-1 inner constants are free in their residue classes and the remaining one is forced. For m=1 the lift is unique.

These fibers and their substitution composition give actual refinement witnesses; the proof does not assert existence of a composition-preserving global section. In fact reduction from the one-interface affine calculus over Z/4 to that over Z/2 has no calculus-homomorphic section. To prove this, let the lift of binary addition be μ=(b;a,c). Associativity forces a²=a and c²=c; unit coefficients therefore force a=c=1. Let the lift of translation by 1 be τ=(t;u), where t is odd. The equation τ μ=μ(τ,id) forces u=1 by comparing the second input coefficient. But τ²=id would then force 2t=0 modulo4, impossible for odd t. Thus our actual arrow lifts do not amount to a global composition-preserving section. The weaker nonsplitting of additive reduction alone would not suffice to prove this, because a putative lift of a translation could initially have a nontrivial slope. The lifting lemma depends crucially on unit outer coefficients and at least one slot. For contrast c(x)=2x modulo4 maps the domain class {0,2} to {0}, not the target class {0,2}; saturation fails without invertibility. Nullary fixed-source lifting is not covered.

## 7. What this contributes and what remains open
The model verifies the general theorem's hypotheses in an unbounded, non-graph calculus, supplies an explicit complete assembly presentation and separately verified cut/transport identities, a non-naive cut/transport interchange calculation, hereditary overlapping-view reconstruction, and exact original refinement lifts with nontrivial witness fibers. It separates three notions often confused: quotient reconstruction, chosen normalized cuts, and actual fixed-endpoint factorization lifting.

It does not establish an unknown physical architecture discovery algorithm, arbitrary interface restrictions, all nullary/empty-sector cases, order-changing crossing interchange, or the original graph-dependent contract's C5/G2/I4/I5 obligations. It also does not make the whole affine theory novel. Any general framework claim must be judged against its independent theorem and prior-art comparison.

Verification: accompanying exact finite checker covers CRT compatibility/fiber counts, presentation equations, substitutions, normalized cut and coordinate transport identities, nested tree telescoping, and fixed-outer forest lifting. These are reproducible finite checks, not Lean verification or a substitute for the proofs above.

## 8. Genuinely overlapping interval families
Let a finite family of nonempty intervals in {1,...,n} be given; intervals need not be nested. Split the ordered frontier at every interval start and immediately after every interval end. This gives disjoint atomic segments S1,...,Sr. Each original occurrence belongs to exactly one segment. For each segment S with first position s define h_S=sum_(j in S)(a_j/a_s)x_j. The common segment-level outer operation is b+sum_S a_s y_S.

For any interval I beginning at i, the segments contained in I are consecutive and cover it. Recover its inner operation by

    h_I=sum_(S contained in I) (a_first(S)/a_i) h_S.

Recover its outer cut by grouping those segment-level inputs with the same coefficient ratios. Both are exact identities. Hence the cuts I=[1,3] and J=[2,4] coexist through segments [1],[2,3],[4], although no planar tree has both I and J as subtrees. The common middle segment is ONE shared node of the witness diagram, not a copied occurrence or an illicit extra variable. This result is a joint diagram of several factorizations through a common ordered segmentation, not a claim that overlapping cuts are themselves simultaneously nested factors in one tree.

Adding intervals only subdivides segments. The normalized factorization of a segment into smaller segments has coefficients a_first(smaller)/a_first(larger); ratios telescope. Therefore the comparison maps for successive segment refinements compose exactly, regardless of the order of insertion of interval endpoints. Recovering any requested cut before or after these comparisons agrees. This proves finite-family cut coherence, including nonlaminar interval families, without permuting the frontier.

Coordinate transport adds one gauge t_S to each shared atomic segment. Its slope is u_first(S), translation sum_(j in S)(a_j/a_first(S))v_j. The displayed recovery formula implies that transporting and then grouping gives exactly t_I for every interval I: the translations sum to sum_(j in I)(a_j/a_i)v_j and the pivot slopes cancel in the normalized ratios. Thus the entire shared diagram, not just isolated cuts, transports coherently. Sequential changes obey the cocycle from section4, and segment refinement comparisons obey the same telescoping identities. Reduction modulo each view preserves all these equalities. Consequently joint families may be reconstructed from compatible modular descriptions with the same occurrence/interval family, and their actual residual operation data are retained.

This does not solve arbitrary crossing partitions. For a four-element 2x2 grid, row-major and column-major products have different ordered frontiers; an operation exchanging the middle occurrences is NOT part of this planar model. The theorem concerns arbitrary finite overlapping INTERVAL families on a single ordered frontier, not every nonplanar cover.
