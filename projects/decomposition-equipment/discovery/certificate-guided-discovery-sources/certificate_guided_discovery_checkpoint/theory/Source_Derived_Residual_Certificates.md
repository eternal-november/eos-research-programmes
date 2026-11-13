# Source-derived residual certificates for requested decompositions

Status: proof candidate, 29 October 2026. Generic relational elimination and finite-algebra minimization are classical. The programme-level construction below connects those tools to the actual original C5 normal forms and to specified finite-interface witness constraints. It does not prove generation or equality completeness for all cells of the original ordinary envelope.

## Plain-language abstract

A simplified description may deliberately forget where component boundaries lie. A proposed decomposition can nevertheless be useful if we recover concrete boundaries only for the uses we intend to make of it. The procedure here turns those requested uses into constraints on actual occurrences, partitions and interfaces, solves their shared choices together, and keeps the possible boundary completions as a residual certificate. Combining certificates means matching the same actual boundary choices, not merely matching their simplified descriptions. A second construction determines which differences between residual certificates can be forgotten safely for a declared collection of future uses. This gives a hierarchy of task-dependent guarantees instead of requiring every abstract refinement to lift between every concrete pair. The method is finite and constructive under stated representation bounds, but can be expensive. Its parameters count the joint witness information, rather than only physical wiring.

## 1. Exact target and finite budgets

A request consists of a finite, occurrence-named diagram D. Its nodes are original C5 operations or explicitly specified local interface relations; its edges identify actual shared variables. Some operations, scalar values, component types and endpoint witnesses are fixed; other values are unknown. Each unknown has a finite declared domain, represented explicitly or by elementary finite constraints as below. In particular, the number of requested component occurrences and the number of unknown ports are supplied by the proposed diagram. The theorem does not infer an unbounded number of components in one step. A proposer may search such diagrams; the theorem solves their jointly constrained realization problem.

A partial view is a computable predicate on a local concrete normal form. For a genuine quotient view this predicate tests membership in the proposed quotient class. Multiple views impose multiple predicates on the SAME underlying variables. No hypothesis says that all quotient refinements lift, that the quotient identifies a unique whole, or that its class consists of a single partition.

Observed records can be included as finite constraints on a declared candidate model, but this alone certifies consistency with those records, not the actual environment or persistent behavior. A model-class and behavioral correctness theorem must separately justify the interpretation of those constraints. The construction is exact relative to its declared finite domains and local predicates.

Specified-endpoint requests fix the relevant original outer and target variables. Existential requests leave them free in their declared classes. Thus these two contracts use one compiler but different pinned variables. Universal fixed-endpoint lifting would assert nonemptiness for every eligible pinning; it is not an admission requirement.

## 2. Compact compilation of actual original C5 operations

Fix the original parameters N, finite category K and finite commutative monoid M. An operation with output (G,f), |G|=r, and ordered full input path ((G_i,f_i))_{i=1}^k has a concrete normal form precisely when:

* sum_i |G_i| = r;
* for each occurrence i, a strictly increasing embedding e_i:[|G_i|] -> [r] is chosen;
* the images of all e_i are pairwise disjoint and cover [r];
* G_i(s,t)=G(e_i(s),e_i(t)) for every i and every local pair s,t;
* the arrows f_i form the prescribed full path and their composite is f;
* a scalar m in M is retained.

These constraints are exactly the original ordered-partition normal form under U_i=image(e_i). Strict increase is substantive: it identifies the canonical increasing enumeration, not an arbitrary graph isomorphism. Equal component graphs at different input occurrences have different embedding variables. Empty components have empty embeddings but retain their occurrence, actual arrow and intermediate interfaces. At k=0 the constraints require r=0, coincident outer interfaces and f=id; the scalar m remains an arbitrary element of M.

The constraints are polynomial in the explicit graph/profile encoding and occurrence sizes. They do not enumerate the set of ordered partitions. All-different can be expanded into pairwise inequalities because the number of listed embedded vertices is exactly r. Induced-graph constraints use adjacency bits directly. If component graph entries or arrow values are unknown within supplied bounded domains, the same predicates constrain those variables; the claim is then relative to those size/interface budgets.

### Primitive and substitution equations

The identity has e_1(j)=j and scalar 1. A binary C generator fixes its two embeddings to the canonical enumerations of its labelled U,V and scalar 1. U_A fixes the nullary data just stated and scalar 1. D(W,m) has the identity embedding and its named scalar m.

For a substitution of inner operations at each named occurrence i, write e_i for the outer embeddings and d_{i,j} for the inner embeddings. Introduce expanded embeddings h_{i,j}, retaining the actual slot-expansion correspondence. The complete defining constraints are

    h_{i,j}(t) = e_i(d_{i,j}(t)),
    m_out = m_outer * product_i m_inner,i,

with all complete component/arrow profiles checked. These are local finite equations. They are neither an oracle for abstract realizability nor enumeration of all whole witnesses.

**Lemma 1 (exact original compiler).** Satisfying assignments of these constraints are in bijection with original C5 normal-form operations and actual occurrence-wise substitutions, with every unknown partition retained. Fixed normal-form endpoints are fixed literally. Every extracted operation has an original syntax representative obtained by the existing labelled right-comb compiler, with the empty and singleton cases handled separately. The precise historical predecessors are `references/original_C5/A3_LOCAL_COMPARISON.md` §§5–6 and `references/original_C5/THEOREM.md` §§5–6; the verified originals are bundled unchanged at those portable paths.

Proof. The embedding constraints recover the unique ordered partition U_i, and conversely its increasing enumerations satisfy them. The induced graph and arrow checks are exactly the source definition of FlatCut. The substitution formula is the source's increasing-enumeration composition formula. The original presentation theorem identifies these normal forms with the quotient by exactly R, UL, UR, D0, DA, DL, DR and supplies the right-comb representative. Therefore no additional semantic operation is assumed generated. QED.

**Lemma 2 (original equations and arbitrary finite grafts).** Replacing a request's original syntax by any of the seven original generating equations, in any typed context, preserves its projected relation on the SAME retained external normal-form variables, after all unrequested internal syntax variables are eliminated. Substitution chains flatten independently of parenthesization. This is not a bijection of raw derivations or scalar factorizations. If an internal child scalar, partition or witness is itself a requested endpoint, an observation, or is constrained by another branch, that variable and its constraints are part of the request; an equation that deletes it is not a comparison of the same request. The lemma applies only to unobserved auxiliary syntax coordinates whose sole constraints are the defining interpretation equations, or to contexts in which all additional constraints are explicitly transported and proved equivalent.

Proof. R identifies the same composite embeddings e_i d_{i,j} g_{i,j,k}; associativity of function composition gives equality. UL and UR delete only a genuinely nullary empty/id block, leaving every named external occurrence untouched. D0 and DA use the identity and associativity of M. DL and DR move the same scalar factor without changing embeddings. Contextual replacement follows by applying the same substitution equations at the parent; induction handles arbitrary finite depth. The scalar products agree by the stated commutative-monoid laws. This proves equality of the projected relations, not a bijection of redundant raw syntax decorations or of specified factorization witnesses. QED.

Several requested cuts can share embedding or component variables. Those shared variables enforce crossing consistency. Different planar orders are not silently identified: if two branches order shared atoms differently, their complete profiles remain different and any required comparison must be explicitly well typed. No exchange or braiding rule is added. Existence of an atom assignment or common refinement is decided by the constraints, not posited.

### A genuine boundary-forgetting quotient, with positive and negative requests

For every original parallel fibre retain the full output (G,f), full ordered input path and scalar m, but identify all admissible partitions with that data. This is a genuine substitution congruence: the expanded path and product scalar are independent of embeddings, and both sides of a well-typed substitution exist by the calculus laws. Its operation fibres contain one element per m whenever the profile is realizable, and are empty otherwise. The quotient therefore genuinely forgets partition boundaries, not merely a display annotation.

Take the edgeless graph on two ordered vertices, input path two copies of the one-vertex graph with identity arrows, and scalar 1. The partitions a=({0},{1}) and b=({1},{0}) are distinct and have the same quotient. The quotient identity forest is a refinement between their classes. Its requested lift from a to a exists and the compiler finds it. Its requested lift from a to b is impossible because all unary inner embeddings preserve the outer blocks. The compiler returns the empty relation. Thus acceptance of this quotient does not require universal fixed-endpoint lifting, while individual requests remain exact.

This example calibrates the contract, not the difficulty of discovery. The quotient retains the entire output graph G and does not infer an unknown environment from observations. The separate dynamical specialization must supply that burden; one must not label this simple graph example architecture identification.

## 3. Finite-interface relations and noninvertible change

For a named finite span A <-l- S -r-> B, a witness variable s ranges over its ACTUAL apex S, not only its endpoint pair. Two distinct apex witnesses with equal legs remain distinct. A seam between spans S and T imposes r(s)=l(t), and stores the pair (s,t). A map f:A'->A gives restriction witnesses (a',s,b') satisfying f(a')=l(s) and g(b')=r(s). These elementary equality constraints compile pullbacks without an inverse-choice oracle. A noninjective map may produce several lifts; a nonsurjective map may leave no lift.

A coefficient map phi between already declared finite witness carriers is represented by its actual table values and its endpoint equations. If that map is an UNKNOWN, its values are shared variables wherever the same coefficient map is used. Solving independently for each call would be unsound. Explicit table size and carrier size count toward input/certificate complexity.

**Important source boundary.** These finite-interface constraints describe concrete span semantics. An arbitrary satisfying coefficient table is NOT thereby a cell generated by the original ordinary envelope. For a request demanding original-envelope derivability, each such table must come from a supplied well-typed syntactic derivation using the actual constructors, or from a separately proved complete compiler for the selected sublanguage. This note supplies that complete compiler for C5, not for arbitrary new envelope cells. Equality of two new semantic tables is likewise not claimed to prove their syntactic equality.

Nullary interface witnesses retain the sole common vertical value. For a unit relation the original constraint is a=b. After applying f on both endpoints the relation is f(a')=f(b'), the kernel pair. Requiring the SAME new lift instead gives a'=b'. Both relations are constructible, but they answer different requests. In particular, the kernel pair must not be replaced by the diagonal when f is noninjective.

All genuine tuple reassociations preserve actual apex variables. Thus iterated pullbacks have canonical bijections given by tuple flattening; no equality of different old apex witnesses is introduced. This supplies coherent finite-interface witness transport for each represented request, not a strict inverse to every original cut comparison.

## 4. Residual relation and witness extraction

Compile the complete request to variables V with local factors F_alpha on scopes S_alpha. A factor is an explicitly evaluable finite relation derived above, a supplied observation predicate, or a separately justified semantic mechanism relation. Let B subset V be the named variables needed by future requests. All world parameters, shared-source variables, original endpoints and occurrence choices that may be referenced later must be in B or in a retained witness store linked to B; they may not be independently resampled.

The residual certificate is

    R_D(B) = {b : exists x on V\B, every F_alpha((b,x)|S_alpha)}.

This formula specifies the desired semantics, but is not the algorithm. The algorithm is bucket elimination: choose an elimination order; gather every current factor involving the next variable v, form their natural join, project v, and store a backpointer relation recording all eliminated v values for each remaining assignment. Factors not involving v remain untouched. Repeat until only B remains. Extract a requested witness by picking an accepted final tuple and following the stored backpointers in reverse order. For existence-only certificates, one valid backpointer per tuple suffices; retaining ALL actual witnesses requires all pointers or a lossless shared representation.

**Theorem 3 (constructive residual exactness).** Bucket elimination returns exactly R_D. A backtracked assignment satisfies every original local factor and therefore reconstructs all original C5 operations/forests through Lemma 1, together with the requested finite-interface witnesses. If the final relation is empty, no realization exists within the declared domains and predicates.

Proof. At each step existentially quantifying v distributes over factors not containing v. Every possible extension of the remaining variables is represented precisely by a row of the join/project factor. Stored preimages witness the existential quantifier. Induction proves the invariant and reverse backtracking. This is standard variable elimination; Lemmas 1–2 supply its exact source-calculus interpretation. QED.

An empty result is a scoped obstruction, not automatically a short independently checkable impossibility certificate. Full elimination tables form a checkable exhaustive proof if their completeness is verified from the factor tables; their size may be large.

## 5. Composition and crossing requests

Suppose requests D and E share exactly the named boundary variables I and have disjoint internal variables after hygienic renaming. If all variables needed later are retained, then

    R_(D union E) = projection_B (R_D natural-join_I R_E).

The proof is distribution and reassociation of existential quantifiers with shared names preserved. It holds for arbitrary cyclic crossing diagrams, not only trees; cycles increase the elimination burden but do not invalidate the equality. Associativity holds as equality of final boundary relations. Witness provenance is associated by canonical flattening of tuples, not deletion of duplicate-looking witnesses.

For local interface change given by an explicit relation T(B,B'), the changed certificate is projection_B'(R_D join T). Composition of changes is relational composition with all truly shared variables kept. A future request that refers to an old B value requires that B remain retained. Projecting it out and later pretending an arbitrary representative may be recovered is invalid.

Consequently the construction supports on-demand exact endpoints while allowing quotient views to forget partitions. It does not make all fixed-endpoint lifts exist. The original identity-forest obstruction becomes an empty concrete factor relation for the offending endpoints, as it should.

## 6. Costs and structural parameter

For explicit finite variable domains of size at most d, let w be induced width of the chosen elimination order on the ACTUAL factor scopes, and let t be the number of elimination buckets. Table construction uses O(t d^(w+1)) local assignments up to factor evaluation and encoding costs; a more precise heterogeneous bound sums products of the domain sizes in each bucket. Final boundary output size and its construction are additional: a relation on b retained variables may contain d^b rows even when internal elimination is cheap. Backpointer storage is bounded by the same processed table sizes for one witness per row. Enumerating all full witnesses can be exponentially larger than finding one.

The width is not physical wiring width. It includes shared whole/model parameters, repeated uses of coefficient tables, temporal source ownership, endpoint equalities and unknown alignments. Splitting one shared variable into fresh copies to reduce width changes the problem. Finding a low-width order is another search problem; a supplied order and its scopes are easy to check. Binary-encoded multiplicities and succinct transition rules must be charged by their actual evaluation/expansion costs. No polynomial guarantee in an unexpanded model encoding follows automatically.

The output constructive theorem is therefore parameterized by actual local representation sizes and witness-interaction width. It does not reconstruct the complete global state model as an obligatory first step, but may encounter equally large intermediate relations when the requested decomposition needs that much coupled information.

## 7. What remains a separate burden

This note alone is infrastructure, not the full approved milestone. A useful interacting dynamical family must establish that the local factors express persistent mechanisms, that its task views really forget boundaries, and that some useful requests certify while others fail jointly. It must also exhibit meaningful local representation/width bounds. The report must not advertise a generic CSP encoding as the novel achievement. Full original-envelope cell generation, arbitrary-arity unknown architecture search, model-class validation from finite observations, and global universal lifting are not proved here.

## 8. Task-relative decision summaries are separate from provenance

The companion Task_Relative_Summaries.md applies only to a declared finite continuation language, including its allowed constants, endpoint predicates and join patterns. The unrestricted algebra of all boundary subsets with intersection and nonemptiness has no nontrivial contextual quotient: a singleton continuation distinguishes any two different relations. Thus safe forgetting is relative to actual permitted future uses, not a consequence of quotienting all possible relations.

A minimized decision summary does not replace the concrete backpointer store. If two residual relations give the same answers to every declared future test, their internal witnesses may still differ. Extract a witness from the ORIGINAL request and its stored pointers, or rerun its solver with the requested pins. Never substitute a convenient representative of the decision-summary class when an original endpoint is specified. A new endpoint test or new context outside the declared language requires refinement/recomputation; no guarantee silently extends to it.
