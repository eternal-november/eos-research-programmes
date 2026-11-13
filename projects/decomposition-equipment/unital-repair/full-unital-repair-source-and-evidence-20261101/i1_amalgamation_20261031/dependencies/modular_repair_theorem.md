# I5 modular repair bridge: actual cut pullbacks, optimum reflection, and failure

31 October 2026. **Proved conditional comparison theorem and explicit coefficient families; NOT a discharge of unrestricted original I1.** This addresses the local-repair clause of original I5 (contract lines 686–703). It does not relabel JACM 2000 Lemma 5.13 as a new modular theorem.

## 1. Fixed scope and notation

Use the selected nonempty-input-edge decoration extension of the ordered graph-cut spine. Full profiles remain separate sorts. For each fixed actual graph operation/spine `g`, let `L(g)` be its nonempty input occurrences; coefficients in a monoid `D` give carrier `D^{L(g)}`. Empty inputs have no coefficient. Under substitution, the coefficient at a nonempty leaf `(i,j)` is `a_i b_ij`. A permitted cut shape `c` specifies the outer graph operation, inner graph operations, occurrence maps, and all retained intermediate graph/interface data. Its coefficient witness at `z` is

    W_D(c,z) = { (a_i,b_ij) : a_i b_ij=z_ij for every active leaf (i,j) }.

Joint seed predicates must be pulled back from one local channel or be Boolean combinations of such predicates and the exact common-skeleton predicates. An extra cross-channel predicate (for example equality of two otherwise hidden channel labels) is outside this theorem and can break its initial-observation decomposition. All entries form ONE tuple; a shared `a_i` is not chosen separately for different j. Iterated cuts retain the corresponding finite tree of shared labels. The theorem uses Boolean/set-valued joint factorization matching, not multiplicity, unique lift, or CULF.

Retain the actual shared graph/cut skeleton exactly in initial observations on both source and cut-record sorts. If several actual skeletons share a full profile, this is an extra observation, not a claim that the profile determines them. Otherwise two locally matching witnesses can choose different graph cuts and fail to glue. Structural interface transports act consistently on this skeleton. The principal two-channel transport additionally exchanges channels.

Write `R_D(P)` for the coarsest refinement of initial partition family P stable under the declared S/C operations and common structural transports, assuming the independently established repair calculus. On equivalence relations, finer means smaller. The result below proves a concrete identification of global and local repairs, not existence from scratch.

## 2. Actual conservative comparison for two channels

Let `A,B` be finite monoids and use global coefficients `A×B`. There are literal coefficient projections `π_A,π_B`, and embeddings

    i_A(a)=(a,1_B),   i_B(b)=(1_A,b).

They are sort-preserving substitution morphisms and agree on the entire undecorated all-unit graph/interface subtheory. This shared theory is nontrivial: it includes the graph partitions, induced subgraph occurrences, ordered cuts, identities, and permitted structural interface maps, rather than only an empty signature. Each embedding is retracted by its corresponding projection. Consequently no two distinct operations of either input theory become equal in the comparison model.

The comparison presentation explicitly imposes the cross-channel interchange relation `(a,1)(1,b)=(1,b)(a,1)` along the same branch. It does NOT delete same-channel order: `aa'` may differ from `a'a`. Along each branch, interchange moves the A labels before the B labels while preserving their internal orders; multiplication gives the unique pair of products. All mixed interchanges are compatible with associativity because both sides evaluate to `(aa',bb')`. At separate occurrences, substitutions act on distinct coordinates; at a shared outer occurrence, the same outer pair is multiplied into each descendant. This supplies actual mixed interactions, not a disjoint union of theories.

For arbitrary A,B these retractions prove operation-equation conservativity, not fullness on cut witnesses: the omitted channel could have nontrivial factorizations of its unit. For the selected M_k, every nonidentity transformation has rank less than k, so no product containing a nonidentity can be e. Consequently every cut of an embedded one-channel source has all omitted-channel coefficients e, and the embedding is also bijective on each corresponding fixed-skeleton cut fibre. The same holds for finite monoids with trivial unit group. This supplies an additional concrete cut-certificate transfer in the principal family.

This is a conservative *comparison quotient* of the unconstrained amalgam, with stated interchange equations; it is not asserted to be the categorical pushout of the two presentations. Rewriting/refinement certificates are claimed only insofar as they are represented by these explicitly retained coefficient tuples and graph skeletons. The full original I1 critical-diagram/refinement theorem remains separate.

## 3. The source-preserving cut square

For fixed global source `z=(x,y)` and fixed actual cut skeleton c, projection gives a bijection

    W_{A×B}(c,(x,y)) ≅ W_A(c,x) × W_B(c,y).

Across variable skeletons this is the fibre product over the retained cut-skeleton set, not the product of arbitrary local witness sets. The inverse pairs every corresponding outer and inner coefficient. It is well-defined because

    (u_A,u_B)(v_A,v_B)=(u_Av_A,u_Bv_B).

Thus it preserves the source exactly, the common outer occurrence, each factor, and each intermediate occurrence map. It never glues witnesses merely because their marginal readouts happen to agree.

Moreover each projection is surjective on the fibre **at every fixed global source**. Given a local A witness at x, factor y over the same cut by assigning each outer B coefficient `1_B` and each active inner B coefficient the corresponding source coefficient `y_ij`. This works simultaneously across all children of one outer occurrence. Empty inner occurrences require no assignment. The same construction recursively lifts a specified finite local cut tree, putting units at internal nodes and the given source coefficients at leaves. It also works for B projection. This is the extra lifting fact needed for optimality reflection; bare product shell algebra does not establish it.

## 4. Local completeness combines, and local optimality reflects

Start with global initial observation

    P(z)=(P_A(π_A z),P_B(π_B z)),

including the exact common structural record. Let `Q_A=R_A(P_A)` and `Q_B=R_B(P_B)`. Define

    Q = ker(Q_A π_A) ∩ ker(Q_B π_B).

**Completeness.** Substitution preserves Q by coordinatewise multiplication and local congruence. For C, take Q-equivalent sources z,z' and any joint cut d at z. Local cut stability produces witnesses d'_A,d'_B at the two projections of z', whose entire factor tuples match the corresponding local classes of d. Exact retention of the common cut skeleton forces these witnesses to have the same actual c. The fibre-product inverse in §3 produces one global d' at z' with both local matches simultaneously. The reverse direction is symmetric. Structural transport is coordinatewise and preserves the shared record, so local transport stability suffices.

**Optimality, not only completeness.** Let E be any globally stable refinement of P. Define a local binary relation

    U_A={(π_A z,π_A z'): z E z'}.

Every pair respects initial observation P_A. Each local deterministic one-hole context lifts to a global context by pairing all fixed A coefficients with B units; hence U_A is stable under local contexts. Given a local cut at the first member, §3 lifts it at the chosen *fixed* global source z. Global E stability gives a matching global cut at z', and projection gives a local match related factorwise by U_A. Thus U_A is an observation-respecting substitution-compatible cut bisimulation. The equivalence relation generated by U_A and the diagonal remains such a relation: inverse and relational composition preserve the back-and-forth property, deterministic compatibility, and initial-observation equality; their union over finite chains does too. Therefore this generated equivalence is contained in the coarsest local stable equivalence Q_A. Likewise for B. Consequently `E⊆Q`. Combined with completeness, this proves Q is the coarsest global repair.

This argument identifies exactly why mere restriction of an arbitrary global optimum is insufficient: its projected relation need not initially be transitive, and its cut matching property requires fibre lifting at the fixed source.

## 5. Channel-exchange transport and direct specialization to the target

For `A=B=M_k`, take equal local initial observations P_0 and identical local operator palettes. Then local optima are the same Q_0. The combined partition `Q_0×Q_0` is invariant under the channel exchange `τ(x,y)=(y,x)`. Hence §4 already gives the global simultaneous S/C/T optimum when T is generated by exchange plus the common structural transports. No explicit classification of Q_0 is needed for this theorem.

This specializes to the active M_k×M_k target with arbitrary graph bound N, arbitrary arity including empty occurrences, and arbitrary finite generated cut/context depth, provided the principal repair calculus certifies those schemata. The proof is occurrencewise and does not collapse profiles. Its shared theory is the retained graph/interface spine. It gives neither a general theorem for forgotten graph-cut skeletons nor a proof that an arbitrary independently repaired pair is exchange-invariant.

**Genuine failure on exactly this target.** Give channel A the H-membership observation from `monoid_repair_theorem.md` (`H={e,b,b²}`), and channel B the indiscrete coefficient observation; retain structural data on both. The B local repair stays indiscrete: all permitted fixed cut shapes are nonempty by the unit/leaf construction, and every deterministic map preserves an indiscrete partition. Let Q_A be the local simultaneous repair of H-membership. It separates e from a because the initial observation already does. Independently combining local optima identifies

    z=(e,e),  z'=(e,a),

in the unary one-vertex graph profile. But exchange sends these to `(e,e)` and `(a,e)`, which the same combined partition separates. Therefore the combination is not even T-complete and cannot be the global optimum. In fact the global optimum is `Q_A×Q_A`: T-stability forces the second H-membership observation too; the symmetric positive theorem then applies, while its optimum-reflection proof supplies the lower bound. This is an all-k≥4 failure family, with a nontrivial shared graph/interface theory, not an arbitrary pair of closures. The obstruction is an actual mixed cross-module transport; the positive equal-observation case closes exactly that obstruction. It is not the stronger original I1 failure of convergent presentations acquiring a new equation.

## 6. Stronger non-disjoint scalar-interface family

To make the shared coefficient theory itself nontrivial, fix finite monoids A,K,B with `|K|>1`. Take local coefficients `A×K` and `K×B`, shared coefficient theory K, and global coefficient pullback

    (A×K) ×_K (K×B) ≅ A×K×B.

Embeddings into global coefficients are `(a,k)↦(a,k,1)` and `(k,b)↦(1,k,b)`, agreeing on `(1,k,1)` and retracted by local projections. Mixed local elements actually interact through the shared multiplication: `(a,k,1)(1,l,b)=(a,kl,b)`; no commutativity of K is assumed or imposed. Thus this is not a disjoint coefficient product disguised as gluing.

Require each local initial observation to retain K exactly at every active occurrence and on cut records. For fixed source and skeleton, global cut witnesses are literally the pullback of local witnesses over the complete K-labelled cut record. When local stability matches a projected global witness at the new source, equality of repaired factor classes implies equality of every K factor, so both local matches automatically lie over the same K record. They therefore glue. A local cut also lifts at every fixed global source: retain its prescribed K tree and choose units at internal nodes and source coefficients at leaves in the omitted private A or B coordinate. Local context constants lift by appending the omitted unit. The completeness and optimum-reflection proof of §4 applies verbatim.

Thus the exact common-separator observation is a checkable sufficient condition for simultaneously gluing matching witnesses; 'local completeness' alone is not. This scalar family is an explicit comparison extension, not a claim that M_k×M_k contains an extra independent K factor. Channel swap can be added when A=B and exchanges the private factors while fixing K, provided the two local initial partitions correspond under that exchange.

## 7. What this does and does not close

Established: actual coefficient operator maps; conservative retractions; shared graph and (in the extension) scalar subtheory; literal joint-witness pullback; fixed-source projection lifting; a proof of coarsest-global-repair reflection; symmetric positive and asymmetric transport-failure controls for the principal M_k² family.

Not established: unrestricted original I1 pushout/coherent-rewriting theorem; arbitrary identification of shared theories; gluing after forgetting the separator/cut skeleton; numerical/objective cut descent; a classification of all modular failures; or a new generic reduced-product shell theorem. These boundaries must remain explicit in the final I5 claim.

## 8. Actual shared-factor matching failure (no missing global generator)

There is a small, explicit failure in the same edge-weighted graph construction with a different finite coefficient palette. Work at graph bound N=1, so at most one active input occurs in any profile; arbitrary empty inputs and unary depth are still allowed. Take the following transformation monoid K on `{0,1,2}` with multiplication `fg=f∘g`:

| index | transformation |
|---|---|
|0|000|
|1|002|
|2=e|012|
|3|020|
|4|202|
|5=t|212|
|6|220|
|7|222|

Its complete multiplication table (row times column, order 0,…,7) is

    0 0 0 0 0 0 0 0
    0 1 1 3 4 4 6 7
    0 1 2 3 4 5 6 7
    0 0 3 0 0 3 0 0
    7 7 4 7 7 4 7 7
    7 7 5 7 7 5 7 7
    7 6 6 4 3 3 1 0
    7 7 7 7 7 7 7 7

Associativity follows independently from transformation composition, and closure is directly displayed. Define local partitions

    P = { {e}, K\{e} },
    Q = { {e,t}, K\{e,t} }.

Both are multiplication congruences: their first blocks are submonoids, complements are two-sided ideals, and quotient multiplication is the two-element meet monoid with first block as unit. Both are also binary-joint-cut stable. For either partition, every source in its first block has exactly factor-class signature `{(E,E)}`; every source in its other block has exactly `{(E,N),(N,E),(N,N)}`. Unit insertion realizes the mixed pairs. The NN pair is realized for indices 0,1,3,4,5,6,7 by respectively `0·0,1·1,1·3,1·4,5·5,6·1,7·7`; omit 5 for Q. The table excludes every other pair. Thus they are their own local simultaneous repairs, including all iterated factorization cuts by binary induction.

But their combined partition R has three blocks `{e},{t},D`, where `D=K\{e,t}`. Sources 0 and 1 lie in D. Source 0 has cut `0=0·t`, with R-signature `(D,{t})`. Source 1 has no such cut: column t of the table has values only 0,3,4,5,7, never 1. Yet each local abstraction separately matches this source-0 cut at source1:

* P uses `1=1·1`, since P(t)=P(1)=N;
* Q uses `1=1·e`, since Q(t)=Q(e)=E.

These witnesses have incompatible actual shared second factors. Therefore the two locally complete cut certificates do not glue, despite identical cut operators and no omitted transport/context generator. This is precisely failure of matching in the shared-factor pullback, not a generic closure counterexample.

To make both local theories properly larger than their intersection, use coefficients `A×K` and `K×B`, sharing K, with any nontrivial finite monoids A,B, and global `A×K×B`. Pull P,Q back from K and ignore the private factors. On the N=1 graph family these are still locally S/C-stable: private cut fibres are nonempty at every fixed source by unit insertion, and no shared outer multiplier must serve multiple active descendants. Their global combination fails on `(1_A,0,1_B)` versus `(1_A,1,1_B)` by the same calculation. Structural interface renaming and private-channel exchange do not remove or manufacture this failure. Taking A=B=M_j gives a parameterized family. Retaining K exactly, as §6 requires, repairs the matching obstruction.

**Boundary:** this is a finite-palette comparison family within the same graph-edge construction, not a claim that this K is a submonoid of the particular M_k or that coordinatewise P,Q stay complete for multi-active-branch profiles at N>1. The N=1 scope is sufficient for a genuine joint-matching obstruction and is stated rather than hidden.

## 9. Scoped presentation and retained-certificate transfer lemma

For the named positive subclass, a concrete presentation can be chosen rather than assuming semantic retractions suffice. Fix the established original common graph/interface spine presentation `(Σ,R)` at its named scope, and retain actual occurrence-indexed refinement forests. This is a relative hypothesis, not a claim that historical acceptance of all C5 obligations is complete. Add a unary coefficient generator `[m]_U` at every nonempty graph object U for each element m of the finite palette, with equations `[1]_U=id`, `[m]_U[n]_U=[mn]_U`. Use exactly the OLD generators Σ with all coefficients 1 as common generators, not an enumeration of all semantic graph operations. Impose branch distribution only for these old generators: an outer unary coefficient pushes to the same coefficient on every nonempty input occurrence, while empty inputs receive no coefficient. Induction on old presentation trees derives this diagonal law for all old composites, exactly as model_and_core_comparison.md Lemma 2 proves; the old relations R preserve its full profiles. A decorated graph operation is represented by the common all-unit operation followed by its input unary coefficients.

For two private channels, add cross-channel interchange at each nonempty U. A fixed finite refinement forest can be normalized by pushing outer labels down its finite branches, then sorting A before B in each leaf word and multiplying consecutive same-channel labels. Every occurrence remains indexed. Both parenthesizations of a path give the same product by associativity; independent branches act on separate coordinates; a shared parent label is copied to every active child on both sides. Same-channel word normalization is terminating by word length; cross-channel sorting terminates by inversions. The sole overlapping multiplication critical triples are associativity, and sorting overlaps preserve the two ordered subwords. Thus the final pair of ordered products is independent of the chosen coefficient reductions on that retained forest. This proves the mixed coefficient coherence needed here, rather than assuming there are no mixed interactions.

A retained refinement certificate in this scoped model consists of the underlying graph refinement certificate in the established common-spine theorem at its named scope plus equality of the two path-products at every final nonempty occurrence. It holds globally iff it holds after BOTH coefficient projections, by equality in A×B. Given two local certificates with the same actual retained graph forest, their coefficient arrays pair entrywise to give one global certificate; conversely a global one projects. The same statement for a cut certificate follows from the source-fixed witness bijection in §3, including all selected intermediate products. Recuts and substitutions of certificates commute with pairing because their formulas use only occurrence copying, deletion of inactive occurrences, and multiplication. Common interface transport acts on the common graph certificate and preserves these formulas. For M_k omitted channels have singleton unit-factor fibres, so embedded local cut certificates are reflected as well as preserved.

For A×K and K×B, use three tagged alphabets for the private A, shared K and private B. The common K alphabet is identified once, not duplicated; private letters commute with each other and with K, but K letters retain their internal order. Normal form is the triple of products. Local retained certificates glue exactly when their K-labelled forests agree, and the exact-separator observation in §6 ensures this for repaired matching certificates.

This is an actual conservative presentation/certificate transfer theorem **relative to the established common graph-spine theorem at its named scope** and the explicitly retained coefficient-forest certificate doctrine. It does not assert reflection of all syntactic proofs in an arbitrary presentation, unconstrained pushout universality, an unrestricted convergent rewriting presentation of the graph spine, or arbitrary quotient-intrinsic cut arrows. Those stronger original I1 requirements remain unproved.

**Explicit N>1 negative check for §8.** Exhaustive common-parent signature evaluation at r=2 and r=3 confirms that neither coordinatewise P^r nor Q^r is locally cut-complete. At r=2, sources `(0,0)` and `(0,1)` have identical initial coordinate observations, but the factor-class pattern “outer in N, both inner factors in E” exists only for `(0,0)`. For P this is immediate because E={e}: both outputs would have to equal the common parent. For Q, E={e,t}; the table shows no a with a in N, `ab=0`, `ac=1` and b,c in {e,t}. Thus the N=1 restriction is essential to the stated locally-optimal counterexample, not merely a missing calculation.
