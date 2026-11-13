# Task relative summaries and the limits of forgetting

Proof note, 29 October 2026. These are standard finite contextual-equivalence and relational facts, specialized to the certificate interface problem. They do not supply the source-calculus compiler or an architecture-identification theorem.

## Plain language abstract

A decomposition certificate can hide its internal construction while retaining exactly the possibilities that matter at its boundary. Further compression is safe only relative to the ways that boundary will subsequently be used. If every possible test or every concrete continuation is admitted, nothing about the boundary's possible values can be forgotten. In particular, checking two branches separately is unsound when their successful witnesses make different choices for the same hidden boundary. A finite declared language of certificate operations provides an exact way to compute which summaries are interchangeable. This computation can be extremely large, and a compressed yes-or-no summary is not itself a concrete witness.

## 1. The first safe hiding operation

A compiled certificate instance has named boundary variables B and internal variables I, with finite assignment domains. Its actual solution relation is R subset Val(B union I). The exact boundary residual is

    res_B(R) = { b : exists i, (b,i) belongs to R }.

For a continuation S on B union J with I and J disjoint and with NO other shared variables, the solutions on the visible boundary satisfy

    res_B(R join S) = res_B(R) intersect res_B(S).

More generally, natural join on all shared variable names followed by projection gives the corresponding equation on any retained output boundary. This follows directly by combining the two existential assignments, whose only possible conflicts are on named shared variables.

This operation can forget distinct original graph partitions and internal derivations. It is safe because all interaction with the intended continuation has been retained, not because every forgotten partition can be reconstructed from every other one. It needs the separator hypothesis: a persistent world choice, shared source, physical alias, or old endpoint later inspected by the continuation is a shared variable and cannot be silently treated as internal.

Concrete witness extraction retains a derivation for each successful boundary row, a backpointer DAG, or enough source information to recompute one. Equality of residual relations is only equality of existential extension behavior at this separator. It does not identify those derivations or establish arbitrary fixed-endpoint lifting.

## 2. Declared finite certificate algebra

Fix finitely many sorts s. A sort includes its full typed named boundary, equality/alias constraints, and any control state needed to state the future-use contract. Let A_s be a finite set of admissible residual relations, each a subset of the finite joint assignment set D_s. The A_s need not be full powersets.

Specify finitely many total typed operations

    f : A_s1 times ... times A_sk -> A_t.

They may be natural joins with specified sharing, projections, renamings, pullback or direct-image relations for interface maps, and nullary residual constants. Availability conditions can be represented by adding a failure element, whose observed status differs from a successful empty relation; alternatively use separate sorts so that every displayed operation is total. Undefined transport and a defined transport with no solutions must not be conflated unless the task explicitly permits it.

Specify finitely many tests o : A_s -> O_o, where each O_o is finite. Examples are nonemptiness, feasibility with a named endpoint request, or a finite resource-budget verdict. Any endpoint whose exact value matters must be represented in these sorts, operations or tests. This does not quantify over unmentioned endpoints.

A context is a well-typed term with one distinguished hole, built from the declared operations with all other arguments filled by admissible algebra elements. Thus context parameters range over the entire admitted carrier, not merely the named nullary primitive constants. An element may occur several times in a term. Sharing a PHYSICAL assignment is a separate semantic constraint: the diagonal operation is

    Delta(R) = { (b,b) : b belongs to R },

not the independent product R times R. A compiler must use Delta or explicit equality constraints when one actual witness is reused. The contextual theorem does not repair a compiler that substitutes independent copies.

Define R approximately_s S when every well-typed context C from sort s to any tested sort gives the same result under every test there.

### Theorem 1 Exact safe summary criterion

The family approximately is the largest many-sorted algebra congruence contained in equality of every declared test. Thus a surjective summary map h_s : A_s -> Q_s supports well-defined declared certificate operations and preserves every declared contextual verdict if and only if its kernel is an algebra congruence contained in approximately.

The requirement that operations descend is explicit. Equality of final verdicts in a single chosen context alone does not imply compositional safety.

Proof. Contextual equivalence preserves tests by the identity context. To show compatibility with a k-ary operation, replace equivalent arguments one at a time. With the other arguments fixed, any output context composed with this one-hole operation is an admitted input context, so each replacement preserves every verdict. Transitivity yields compatibility. Conversely, any congruence preserving the tests preserves every term context by induction, and is therefore contained in approximately. A surjection admits well-defined descended operations exactly when its kernel is a congruence. Its tests and contextual verdicts then descend exactly when that congruence is contained in approximately. QED.

Containment alone does not suffice for an arbitrary encoding: a smaller equivalence need not itself be operation-stable. All uses below require a congruence kernel.

### Constructive computation

Start with the partition P_0 of each A_s by the vector of its declared tests. For every operation f, every argument position j and every choice of all other arguments, form the elementary translation a -> f(...,a,...). Refine P_r by the block identifiers of the outputs of all these translations, together with the old block identifier. Stop when no block splits.

At stability, equal blocks are preserved by every elementary translation, hence by every operation by replacing inputs sequentially. The stable partition preserves all tests, so it is contained in approximately. Inductively approximately is contained in every P_r, because contexts are closed under these translations. The stable partition is therefore exactly approximately. Every split has an explicit distinguishing test-context, obtained by composing the translation causing the split with the previously stored distinguishing context.

There are at most N minus the initial total number of nonempty partition blocks proper split rounds; empty carriers contribute zero. If N=sum_s |A_s| and E bounds the number of elementary translations at any sort, an explicit-table signature implementation uses at most O(N^2 (E+number of tests) log N) elementary table operations, plus construction/storage of the algebra's operation tables and distinguishing contexts. This is only a coarse upper bound; output contexts may be stored as DAGs. It is polynomial in the FULL ALGEBRA tables, not in the original boundary-variable count. If D_s has d^b joint assignments, the unrestricted relation carrier has 2^(d^b) elements. There is no compactness claim.

One can use a reachable operation-closed subalgebra instead of all relations, provided every possible input residual and every allowed continuation value belongs to it. A grammar restricting future contexts more tightly must be compiled into sorts/control states or treated by its own contextual theorem. One may not use all algebra contexts in the proof and then claim an exact minimum for a smaller resource-restricted language.

## 3. A no forgetting boundary

### Proposition 2 Full continuation access forces exact residual support

Let A=P(D) contain every subset of a finite boundary assignment domain D. If intersection is an admitted operation and nonemptiness is an observed test, then approximately is equality.

Proof. If R differs from S, choose b in their symmetric difference. The context C(X)=X intersect {b}, followed by nonemptiness, distinguishes them. QED.

Consequently, merely declaring a small list of tests does not make a full relation algebra compressible. Arbitrary continuation constants already encode all singleton tests. A proposed task-relative compression must restrict future continuation relations, not just omit endpoint tests by name.

This does NOT say every original partition must be retained. Different original certificates may already have the SAME residual boundary relation after eliminating genuinely internal structure. Proposition 2 concerns further compression of boundary support, not injectivity on original witnesses.

### Proposition 3 Per-value existential equivalence does not support joins

Let D={0,1}, and suppose the only standalone test on a value is acceptance of either value. Both values appear equivalent. Let R={0} and S={1}. Each residual is nonempty. If they are represented by the same nonempty abstract value, abstract intersection appears feasible, although R intersect S is empty.

Even declaring the nonempty relations R and S equivalent fails algebraic stability: R intersect R is nonempty while R intersect S is empty. The failure persists with no dynamics and hence cannot be repaired by a temporal argument. It is precisely a disagreement over a shared concrete choice.

## 4. A proper positive restricted algebra

The preceding limit does not make every useful summary trivial. Let T be a finite task-value set, and let D=T times {0,1}. Define A to consist of residuals R with the anchor property

    if (t,1) belongs to R, then (t,0) belongs to R.

Each nonempty task fibre therefore contains its common anchor (t,0). Let h(R) be its projection to T. Allow union, intersection, restrictions by C times {0,1}, and maps (t,j) -> (g(t),j) by direct image, where g is among declared finite task maps. Include nullary constants only from A, and observe tests depending only on h(R).

### Proposition 4 Safe nontrivial forgetting

A is closed under those operations. The map h is a homomorphism to the corresponding operations on P(T), including intersection. Hence ker(h) is a test-preserving congruence and is contained in approximately. In particular {(t,0)} and {(t,0),(t,1)} can be identified despite being different concrete residual supports.

Proof. The anchor property is preserved by each operation. Projection preserves union, restriction and direct image. For intersection, any t in h(R) intersect h(S) has (t,0) in both, so t lies in h(R intersect S). The reverse inclusion always holds. The remaining claim follows from Theorem 1. QED.

This is a calibration of the contract, not an architecture-discovery example. The anchor property is substantive and deliberately explicit. If the continuation family is enlarged to include {(t,1)}, or if exact membership of (t,1) becomes an endpoint test, the displayed identification is no longer safe. A noninvertible g causes no problem for this stated forward direct-image operation, but no inverse witness-lifting claim follows.

For more general admissible relations, safe projection across all joins means precisely that every compatible tuple of projected rows has a joint concrete row. This is not assumed automatically. The source compiler and constructive solver must establish it, or retain the underlying joint relation instead of using this extra quotient.

## 5. Witnesses are not decision summaries

A source instance P carries a realization set W_P and an evaluation map e_P:W_P -> R_P into its feasible boundary rows. A summary h(R_P) records task-context decisions. It does not carry a map from a witness of an arbitrary representative of [R_P] back to W_P.

A sound extraction pipeline therefore either:

- retains source-specific backpointers from accepted rows to derivations in W_P;
- reconstructs those derivations by rerunning exact source constraints after the summary says a request is feasible; or
- separately proves a source-specific lifting map for the requested endpoint.

The cost of those data or recomputation must be counted. If a certificate graph is reused, its world/source variables must be shared under the declared diagonal or equality operation. Independent existential choices cannot be merged by comparing only their summary classes.

A fixed actual target is admitted by adding the corresponding source constraint/test BEFORE solving and compressing. If a new target is requested later and its test is not respected by the old summary, the old summary must be refined or the source reopened. It is not a false negative when a certificate for one endpoint says nothing about another.

## 6. Programme contribution and limits

These propositions explain the hierarchy proposed by the user. Universal lifting demands every eligible representative pair work. On-demand certification asks whether this exact request has a witness and permits internal distinctions irrelevant to the request to be hidden. Compositional use requires retaining every shared choice inspected by the admitted contexts, or proving a task-relative congruence for further compression.

The underlying tools are classical contextual equivalence, congruence refinement and relational algebra. The new source-level burden lies elsewhere: deriving the correct residual relations and provenance from the actual typed decomposition rules, including noninvertible transport and nullary cases, and showing a useful interacting discovery family. This note is not a substitute for those proofs and does not establish a general improvement in search complexity.

## Reproducible finite checks

`tests/check_task_relative_summaries.py` passes 764 counted assertion cases: full-powerset contextual partitions for domains of sizes 1 through 4; the nine-element anchored algebra with its four task classes; a new endpoint test splitting a former class; 256 exact separator-projection pairs; shared-choice/alias failure controls; and disjoint source-witness payloads. These are finite regression checks, not formal verification of the quantified proofs.
