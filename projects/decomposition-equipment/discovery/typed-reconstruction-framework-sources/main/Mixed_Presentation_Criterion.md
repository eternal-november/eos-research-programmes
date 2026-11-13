# A local presentation criterion for cut and restriction descent

**Status:** proved sufficient criterion and an unbounded calibration class; application to the original C5 presentation remains open. This is not an arrow-lifting theorem and does not discharge F3 or I4.

## Plain-language abstract

A quotient can respect assembly and nevertheless forget information needed to cut the assembled object apart. Checking a few whole objects cannot exclude that failure at arbitrary depth. This note supplies a reusable way to check the *presentation* instead: describe each cut or interface restriction by rules that recurse into the immediate children of an expression, and check those rules against each defining equation. If a finite collection of domain and output checks passes, the quotient respects the operations inside expressions of every finite depth. The certificate retains order and actual occurrence identity; it does not turn a crossing into a permutation.

This addresses well-definedness, not the stronger claim that every quotient-level factorization lifts with a specified original endpoint. That stronger claim needs a separate surjectivity test. The concrete unbounded example below establishes the checks for typed paths, including empty paths and partial interface relabelings. It calibrates the method but is not offered as the sought substantive crossing-decomposition model.

## 1. Input data, not a globally assumed cut-stability property

Let `T` be a many-sorted constructor term algebra. Its sorts retain the full ordered profile, whole/component colors, and any named empty-boundary data. Let `E` be generating **parallel** equations, and let `≡E` be their substitution/context congruence. An occurrence variable is not identified with another occurrence merely because they carry equal labels. There is no exchange rule unless expressly part of the calculus.

A **structural residual specification** consists of the following data.

1. A finite sorted domain algebra `D` and a constructor-algebra map `d:T→D`. (An effectively parameterized version is discussed below.)
2. A finite collection `Q` of residual operations. For each state `q` and domain value `a`, the specification says either undefined or gives the ordered list of output sorts. Thus availability is determined by `d(t)`, not by an unexamined semantic predicate.
3. For each constructor `c`, child domain values `(a₁,…,aₖ)`, and state `q`, an undefined clause or an ordered tuple of constructor contexts. Holes in those contexts are filled by specified components of residual calls `q′(tᵢ)` on proper children. An identity residual is permitted. Every required child call must be declared available and every output context must type-check. The result must have the availability and output sorts declared for `q,d(c(t₁,…,tₖ))`.
4. Clauses for nullary constructors, including named units/empty boundaries. These are real clauses, not inferred from an empty product convention.

Structural descent makes all residual operations terminate. The specification must be proved to compute the intended cuts/restrictions on the unquotiented calculus. A convenient but unjustified residual specification is not evidence about a different intended operation.

Dependent profiles can be handled as indices of a typed term family. The finite theorem applies when the actual sorted signature, states, domain values and rules are finite. For arbitrary profiles or interval indices, one instead supplies finitely many parameterized schemes and a proof that their arithmetic/type case split is exhaustive. Calling such a presentation 'finite' without this coverage proof is insufficient.

## 2. The local certificate

For each equation `ℓ=r` and every realizable assignment of domain values to its variables, check:

**D. Domain invariance.** Evaluating the constructor domain algebra gives `d(ℓ)=d(r)`.

**M. Mixed residual equation.** For every residual state `q`, symbolically run the recursive clauses on `ℓ` and `r`, stopping when a residual reaches a variable. Both runs must be undefined, or both must be defined with exactly the same ordered output sorts. In the latter case their corresponding output components must be provably equal modulo `E`.

For this symbolic check, a stopped call is represented by a variable `z[x,q,j]`, where `x` is the original occurrence variable and `j` the output component. Repeated occurrences of the *same* stopped call share the same symbol on both sides. Distinct calls are not silently identified. Identity residual calls use the original variable. The proof of equality is an ordinary derivation in the target constructor presentation, with these typed symbols free.

The criterion is deliberately sufficient: treating different residual outputs of one variable as freely independent can be stronger than their actual correlated semantics. Failure of a symbolic test therefore need not prove that semantic descent is impossible. Conversely, a passed test is a finite derivation that can be instantiated with actual correlated outputs.

For finite input data there are finitely many checks. This does not assume an arbitrary presentation has decidable equality: effectiveness means a finite *verifiable proof certificate*, or a terminating confluent normalizer supplied separately. An automatic decision procedure is available only with that additional equality algorithm. Reachable domain assignments may be overapproximated by all well-sorted assignments; this is safe but may introduce unnecessary failures.

## 3. Descent theorem and proof

**Theorem (local mixed certificate).** If D and M hold, then for every `t≡E u` and every residual `q`:

- `q(t)` is defined iff `q(u)` is defined;
- their complete ordered output profiles coincide;
- when defined, corresponding output components are `≡E`-equivalent.

Consequently all specified cuts/restrictions descend to the quotient. Any finite composite formed from these operations and constructor grafts also descends, with its original partial domain reflected by the quotient.

**Proof.** First D extends from generators to every contextual equation: substitution supplies the variable domain values, and the constructor-algebra property propagates equality through the surrounding context. It therefore extends along an arbitrary finite congruence derivation.

Consider an elementary step `ℓσ↔rσ` at the root. Instantiate the symbolic M certificate with the actual residual outputs of the substituted terms `σ(x)`. Structural recursion ensures that its two sides evaluate to the actual outputs. No inductive assumption that those outputs respect `E` is used: the substitution is identical on the two sides.

Now consider `C[ℓσ]↔C[rσ]`. Induct on the surrounding constructor context, simultaneously for all residual states. Domain equality selects the same recursive clause on both sides. Every call on an unchanged child is identical. Calls on the changed child have congruent outputs by the induction hypothesis for the relevant residual states. Constructor congruence combines those outputs into congruent tuples. Availability and exact output typing are preserved by the same clauses. This proves the assertion for each elementary contextual equation. Transitivity proves it for `≡E`.

For finite composites, induct on the computation: equal quotient inputs have equal availability, and each intermediate output remains equivalent, so the next availability test agrees. Constructors already preserve `≡E` by definition. ∎

**Coherence consequence, with an important limit.** Any diagram identity already proved between actual unquotiented composites descends. The theorem does not create a missing comparison, prove its invertibility, or establish an identity which the original calculus did not have. In particular, two crossing cuts with differently ordered profiles cannot be identified by this argument.

**Why this is not a restatement of global stability.** The input checks refer only to generating equations and recursive clauses, with finitely many domain/residual states in the finite version. The proof supplies arbitrary contextual closure. It never quantifies as a hypothesis over all cut instances on all equivalent terms. The substantial application work is finding a correct residual specification and checking all its mixed equations.

## 4. The separate lifting obligation

For a partial structural map `f:A⇀B` and equivalences `E_A,E_B`, the theorem establishes domain saturation and

`f([a]E_A) ⊆ [f(a)]E_B`.

Fixed-output lifting instead requires the reverse inclusion too:

`f([a]E_A) = [f(a)]E_B`  for every defined `a`.

For a multi-input operation, `E_A` here is the product relation on its actual typed domain, not an equivalence on an untyped Cartesian product containing noncomposable tuples. Domain saturation must be checked there as well. Local output-equation certificates supply no class-image surjectivity. Even stable monoid congruences can fail to lift a desired factorization of a fixed original output.

If class-image equality is separately proved for each node operation, recursive backward lifting on a tree is available. Shared variables in crossing diagrams impose simultaneous constraints; they require an additional relative compatibility/intersection argument, not merely independent nodewise lifting. Nor does a nonempty realization fibre imply a coherent chosen section of all fibres.

For several views, apply the local certificate separately to each presentation congruence. Their intersection is then stable and domain-reflecting. This supplies a structural hypothesis for a separate multiview reconstruction theorem; it does not supply that theorem's compatible-family surjectivity condition.

## 5. An unbounded class whose checks can be established

This example is an explicit calibration, not a novelty claim.

Fix a finite directed multigraph with edge alphabet `A` and vertex set `V`. Witnesses are finite typed edge paths, including the empty path at each named vertex. Constructor syntax uses binary composable concatenation and named units. Let `R` be an equivalence on edges relating only edges with the same source and target. The equations are associativity, left/right unit, and the finitely many generating parallel edge identifications for `R`.

The resulting quotient is exactly letterwise `R`-equivalence of paths with the same ordered vertex profile: normalize parentheses and units, then use the edge relations. In particular, length and every vertex along the path are retained.

Allow cuts `cut_(i,j)` producing the ordered tuple `(prefix,middle,suffix)` for `0≤i≤j≤length`, retaining the two actual cut vertices even when factors are empty. Also allow a finite collection of partial edge relabelings `h` fixing vertices, defined on specified subsets `A_h⊆A`, and mapping each admitted edge to a parallel edge. A path is in the domain of `h` iff all its edges are in `A_h`. Impose the finite conditions

- `A_h` is a union of `R`-classes;
- `a R b`, with `a,b∈A_h`, implies `h(a) R h(b)`.

**Residual clauses.** Transport distributes through concatenation and maps a named unit to the same named unit. Cut residuals split a concatenation by comparing `i,j` with the first factor's length: both points before the join, straddling the join, both after it, and their equality/boundary cases. They concatenate only contiguous residual pieces and subtract the first length for indices in the second factor. The empty-path case is permitted only at indices `(0,0)` and returns three empty paths at the retained vertex. Length/vertex profile and transport admissibility are the domain data. Thus this is a parameterized, not finite-state, instance; the elementary integer trichotomy supplies an exhaustive finite schema proof.

**Check of all generating equations.** Associativity changes only parentheses, so the interval intersections with each of three concatenated paths are identical on the two sides and appear in the same order. Units insert a zero-length interval, so the residual expressions differ only by named unit laws; the cut vertex does not change. A parallel edge replacement preserves length, every cut vertex and transport membership. Cutting that edge either places it in the same one of the three factors on both sides or places it on the same boundary; corresponding factors differ by that edge equation. Transporting it yields an `R`-equation by the second finite condition. These exhaust the generating equations and all positional cases, including empty factors.

The theorem therefore applies to paths of **unbounded length**, arbitrarily nested concatenations, arbitrarily many cuts and any finite composition of the supplied partial transports. A common domain formula is retained: a whole-path transport can be undefined even when transport of a selected subpath is defined. One may not erase that distinction in a putative transport/cut square.

**Additional cut lifting, proved separately.** If a cut output `(u,v,w)` is replaced by a componentwise `R`-equivalent triple `(u′,v′,w′)` with the same retained endpoints and lengths, concatenate the latter triple. The resulting path is `R`-equivalent to the original, and its specified cut is precisely the requested triple. This proves class-image equality for this cut. It does not prove such equality for a general partial transport. For example, take two parallel edges `a R b` and the total relabeling `h(a)=h(b)=a`. All descent checks pass, but `h([a])={a}` is strictly smaller than `[h(a)]={a,b}`. Thus even within this positive class, transport descent need not imply fixed-output lifting.

Multiple interval partitions can be jointly refined by retaining the union of cut positions, with its original linear order. This example does not validate arbitrary subset crossings, nonparallel reordered profiles, or the old C5 span comparisons. Its purpose is to demonstrate that local tests can genuinely cover an infinite class rather than just bounded enumeration.

## 6. Necessary failure controls

1. **Assembly congruence is insufficient.** In a free word algebra impose `ab=cd`, with four distinct letters and no other relations. The quotient respects concatenation, but the length-one prefix cut would identify `a` with `c`, which is false. The mixed output test rejects it.
2. **Output checks alone are insufficient.** Identify two parallel primitive terms `a=b`; make a partial restriction defined only on `a`. Domain invariance fails although there is no pair of defined outputs to compare. Checking defined pairs alone misses this failure.
3. **A single residual state is insufficient.** A surrounding constructor may call a different residual state on the changed child. The induction needs every reachable state, not only the initial one.
4. **Nullary interfaces are substantive.** For finite-span interface restriction, the unit comparison is the diagonal `A′→A′×_A A′`; it is invertible exactly when the interface map is injective. Treating an empty list of internal tests as automatically exact misses this obstruction.
5. **Local invertibility is not implied by descent.** Equality of residual outputs modulo a quotient cannot prove that a comparison map has singleton fibres. Exactness/lifting needs an additional argument.

## 7. Relation to the existing dossier and remaining bridge

The existing `Global_Cut_Repair.md` already proves arbitrary finite planar-tree repair, coherent splits/contractions/rotations/units and exact-graft transport in its declared span setting. Its §10 gives the actual fibre criterion for interface comparisons; it explicitly requires all relevant interval composites, and shows that primitive adjacent-pair checks can miss a longer failure. Its §11 leaves the smaller original C5 generation bridge open. Those results are reused, not reproved or claimed here.

The integrated `Results_Integrated_A4_C5_B3.txt` proves its raw-forest/equation mixed presentation and retains each original occurrence's whole, graph, ordered partition, complete profile, interface arrows and scalar. That establishes its stated syntax/semantic comparison, not arbitrary cut/transport compatibility of every additional quotient.

To apply the present criterion to that actual C5 presentation one must still:

- extract the exact constructor/equation schemes and their full typed occurrence data;
- supply residual rules for every intended cut and interface restriction, including all intermediate intervals and nullary cases;
- prove those rules compute the actual operations, and prove the parameter case split exhaustive;
- discharge every D/M test against the actual generating equations;
- separately establish any required class-image lifting or invertibility criteria and simultaneous crossing compatibility.

For orientation, the **extended**, not C5-only, presentation in `Extended_Local_Presentation.md` §2 has the seven schemes `(S), (D1), (D2), (N2), (N0), (A), (U)`. Its binary naturality `(N2)` requires the same actual middle map on both sides; `(N0)` retains nullary whiskering; `(A)` uses actual tuple-rebracketing bijections rather than literal pullback equality; `(U)` deletes only the specified diagonal unit. A residual check must retain exactly those qualifications. Merely counting seven scheme names does not verify the new mixed tests.

No such C5 residual table has been verified in this note. Therefore this is a proved general conditional **descent tool**, with an established unbounded calibration class, not the completion of F3/I4 or a new general reconstruction theorem. Its method is a structural-recursion/congruence argument; novelty is not inferred from this formulation.
