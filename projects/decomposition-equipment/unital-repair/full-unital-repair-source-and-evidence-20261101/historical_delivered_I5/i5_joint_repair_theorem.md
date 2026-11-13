# Simultaneous observational repair of graph-linked branch witnesses

**Theorem package — 31 October 2026. Selected-family result with separate proof, coverage and reproduction reviews.**

The scope is specified in `concrete_model_gate.md` and stated below. This package does not adopt RC0.2, close the entire original contract, or impose universal endpoint lifting on task abstractions. The proof and review reports distinguish the selected mathematical result from broader original obligations and physical applications.

## 1. Result and exact guarantee

For every graph bound N>=2 and k>=4, take the original finite-K ordered graph-C5 calculus with terminal original scalar, retain all its operation/profile data exactly, and enrich each nonempty input occurrence by a two-channel transformation witness in `L=M_k×M_k`. Empty inputs carry no additional label. A branch label multiplies into each nonempty descendant under actual substitution. Permitted interface change is the specified channel-frame swap. Permitted cuts are all generated finite planar ordered cut trees, retaining their actual old skeleton and ONE jointly compatible tuple of factor witnesses.

The initial observation records, at each active input, only whether the FIRST LOCAL channel belongs to `H={e,b,b²}`. It ignores the second channel. The result is:

> **Principal theorem.** The coarsest typed refinement of this observation complete for the declared substitution, Boolean joint-cut experiments and channel transport is the full active-label tuple, while retaining the already-observed old data. Over any fixed old record with r active inputs it has exactly `(3k−2)^(2r)` classes. This holds among ALL profilewise partitions, not only uniform, product or bounded-memory representations. It covers unbounded generated arity and depth through explicit local schemata; it does not identify full profiles.

The same witnessed class has a proper finite-group quotient positive control for which one transport pass gives the optimum without recovering all labels. On the M_k family, substitution and cut repairs do not commute; an exact elementary-cut stabilization hierarchy requires `max(2,ceil(log2(k−2)))` strict rounds in the unary slice. This is an unbounded order-dependence family and a logarithmic lower bound for the specified elementary signature algorithm, not an assertion that every algorithm needs that many rounds or that saturated-repair alternation grows unboundedly.

The judgment is exact truth of the declared finite generated experiment language: initial observations, Boolean operations, typed context/transport pullbacks, and existential JOINT cut modalities. It does not preserve multiplicity, actual selected witnesses, isotropy, unique lifting or CULF. It does not prove physical sensor access or controller transfer. A cut modality asks whether ONE record realizes all specified factor tests simultaneously; independent marginal witnesses are invalid.

## 2. Concrete witnessed family and its presentation

### 2.1 Old structure remains visible

An old operation retains its whole graph G, actual ordered partition pi, complete grade/interface path and occurrence positions. Equal labels at two occurrences do not merge them. Graph bound N does not bound profile arity, empty inputs or unary chains. For each old operation α define `Act(α)` to be its nonempty input positions, of cardinality r<=N. An enriched operation is `(α,l)` with `l in L^r`. Its full sort is the original FULL profile, not merely r; multiple old witnesses in one profile remain distinguishable by the initial readout.

For substitution α[β_i], a nonempty resulting input (i,j) receives `l_i m_ij`. Every such input has nonempty ancestors, so the factors exist. Identity has label e on a nonempty component and no labels on an empty component. Associativity follows along each individual nonempty root-to-leaf path; labels on independent branches never need to commute.

The two frame copies have interfaces `(A,f)`, f∈{0,1}. Transport toggles f and interchanges the two witness channels, leaving old K arrows and planar occurrence order unchanged. For M_k acting on [k], the channel interface is `B={0,1}×[k]`; `(x,y)` acts block-diagonally, and the actual permutation `(c,z)↦(1−c,z)` conjugates it to `(y,x)`. Thus T is genuine specified interface-frame change, not all arbitrary maps or leaf exchange.

### 2.2 Reusable local presentation and old comparison

`model_and_core_comparison.md`, Theorems 1–3, proves the extension from the original presentation `(Σ,R)`. Adjoin unary generators D_H(l) on nonempty components, monoid relations, and the local relation

`D_out(l) ∘ g = g ∘ (D_input(l) on nonempty inputs; id on empty inputs)`

for each OLD generator g. The old presentation dependency is pinned in `model_and_core_comparison.md` §7: `original_C5/THEOREM.md` §§2–6 gives the exact finite signature and old semantic completeness; integration `Completion_Comparison.md` Theorem 6.2 supplies the specified common-spine occurrence-forest comparison. Their bundled relative paths and SHA-256 hashes are listed there. Neither automatically covers our new relations. Every extended term normalizes to an old term followed by one D label on each nonempty external input. This proves relative soundness/completeness, not merely an operation-level construction. The all-e inclusion and label-forgetting retraction conserve old operation equality on every full profile.

Every old cut tree of α lifts to a cut of any `(α,l)`: put the desired labels at external active leaf edges and units on internal edges. Therefore old label-blind existential cut judgments are preserved and reflected. No cut-fibre bijection is claimed; units may create extra nonidentity factorizations of an all-e label. This is a conservative explicit enrichment of the old language, not replacement of its commutative global scalar by an illicit noncommutative scalar.

## 3. Observation, information order, and the three repairs

Fix the concrete carriers and all permitted operations before repair. On each full typed sort an abstraction is an equivalence E. Write

`E <=info F  iff  F subseteq E`.

Thus F retains more information. Every repair refines its INPUT, not just the original E0. For a deterministic partial operation g, stability requires equal definedness and E-equivalent outputs. The concrete-to-abstract map is `X→X/E`; if F refines E, the comparison is `X/F→X/E`.

* **S(E):** coarsest refinement stable under generated occurrence-wise grafts, with all other actual arguments fixed. Elementary one-hole substitutions generate arbitrary contexts by syntax induction.
* **C(E):** coarsest refinement stable under joint cut signatures. For a fixed old cut c of x, its actual records include entire outer and inner label tuples, with `x_ij=a_i b_ij` and one shared a_i for all j in the group. Define `sig_c^E(x)` as the SET of full tuples of factor E-classes attained by actual records. E-stability requires equality of these sets for E-equivalent sources. Old cut skeletons are retained exactly, not amalgamated by marginal agreement.
* **T(E):** coarsest refinement stable under the actual frame swap and its inverse, not all conceivable interface transports.

These are individually saturated repairs. A “one-pass” statement concerns their composition, not one elementary signature split. For finite closed typed systems, the standard partition-refinement argument proves existence, extensivity, monotonicity, idempotence and leastness: split blocks by present class, deterministic output classes and joint cut signatures until fixed. A stable finer partition survives every split because its matching joint witness projects to a matching coarser tuple. This argument never assumes arbitrary intersections of bisimulation equivalences are stable.

The generic finite algorithm and exact Boolean polyadic experiment-language theorem are proved in `repair_calculus.md`, §§2–4. Its §8 also establishes existence of each separate repair over the INFINITE full-profile family: every fixed old cut skeleton has finitely many label records and finite arity, so equality of all finite generated modal formulas is stable by a finite conjunction excluding all candidate mismatching records. Infinitely many profiles and cut names are allowed. This image-finite argument asserts no finite global enumeration or convergence bound. Generic shell/minimization machinery is baseline infrastructure, not the claimed decomposition-specific advance. For the infinite full-profile principal family, §6 below gives an explicit optimum and necessity proof without assuming a finite quotient of old profiles.

## 4. Complete generated-operation schemata and their limit

Over r active inputs, every elementary ordered cut reduces on NEW labels to a monotone surjection `g:[r]→[m]`, with positive group sizes and m<=r<=N, and equations

`x_j=a_{g(j)} b_j`.

There are `2^(r−1)` active grouping patterns when r>0; the zero-rank case has a unique label tuple. Each actual old skeleton retains all omitted empty positions, graph embeddings and grade arrows. Over EACH fixed admissible old skeleton, all and only solutions of these equations are decorating witnesses. This is fibrewise surjectivity, not permission to apply a grouping at an invalid old profile.

Grafting reads the same equations as a function. Fixing all but one input gives one-hole templates. Arbitrarily long unary chains use repeated multiplication; label-free empty-only nodes introduce no new independent coordinates. Transport is the finite channel action. Arbitrary finite planar cut trees are obtained by these nodewise relations. To match a tree, match the root JOINT record and then the child subtrees while retaining the chosen child source; distinct subtrees have no additional cross-sibling hidden variable beyond the retained parent. This proves coverage for the stated tree grammar, not crossing cuts or extra unrecorded correlations.

**Important limitation.** A finite label-template list with exact old guards does not by itself prove a generic finite minimization theorem for every possible old-profile-dependent E. Some profiles might support fewer templates. We make no such claim. The principal optimum is instead proved by concrete identity-operation tests available at EVERY old record, and its sufficiency is discrete. Thus no unsupported finite old-profile normalization is needed. Arbitrary-E finite-fragment bounds below apply only to genuinely closed finite systems or separately certified finite schema representations.

## 5. Analytic monoid family and genuine noncommutation

Use composition `fg=f∘g` of transformations of `{0,...,k−1}`:

`a=(k−1,1,1,2,...,k−2)`, `b=(1,2,1,...,1)`.

The full analytic multiplication/normal-form proof is `monoid_repair_theorem.md`. With t=k−1, its distinct forms are

`A_i=a^i (0<=i<=t)`, `B_i=ba^i (0<=i<=t)`, `D_i=b²a^i (0<=i<=t−2)`.

There are 3k−2 elements. The exceptional merge is `b²a^(t−1)=A_(t−1)`, not A_t. H={A_0,B_0,D_0} is a submonoid with ideal complement, so membership in H is a multiplication congruence. Equivalently the initial bit records whether a branch transformation can be generated using only b, versus having passed through the designated a stage: every word containing a lies in the ideal, and every word without a lies in H. This is a named coarse process readout; no empirical hazard meaning is inferred from it. Consequently the coordinatewise initial observation is already S-stable under the FULL branchwise graft law, not only unary multiplication.

Let h(A_i)=h(B_i)=h(D_i)=i and Q=ker(h). For unary factorization,

* if h(x)=i<t, the possible index pairs are exactly `(j,l)` with j+l=i;
* if h(x)=t, they are `(0,t)` and every `(j,l)` with 1<=j<=t and 0<=l<=t.

Q is therefore cut-stable. Conversely, generated cut tests count the maximum number of factors outside H: a nonconstant of index i permits at most i, while the constants permit arbitrarily many. Thus `C(P0)=Q` on M_k.

But `e Q b`, whereas left multiplication by a gives `a` of index 1 and `ab=A_t` of index t. Hence Q is not S-stable. The full graph-C5 conclusion is justified by the single-vertex spine theorem: every cut of a one-vertex whole has one nonempty spine and exactly the monoid factorization equations; empty branches have unique labels. Unary insertion realizes every binary factorization. A Q-stable family on all one-vertex sorts extends to a C-stable family by taking discrete partitions on larger graphs, so there is no hidden higher-arity cut backpressure. This proves equality with the unary C repair, not just an inclusion.

For the two-channel seed, cut fibres factor by channel and the second indiscrete observation is stable because every cut shape has a factorization. Thus this same unary noncommutation survives with L=M_k². Since S(E0)=E0 but C(E0) fails an actual unary graft, `S C(E0) != C S(E0)` for every k>=4. These witnesses are within fixed full profiles of the declared graph family, not two unrelated lattice closures.

## 6. Exact simultaneous optimum on ALL full profiles

### 6.1 Finite monoid necessity

`monoid_repair_theorem.md`, §4, proves that every S/C-stable refinement of H-membership is discrete:

1. It must retain the index h by C-completeness.
2. Left multiplication by a separates A_i from B_i,D_i for i<=t−2, in particular isolating A_1.
3. The joint cut predicate “there is a factorization with left factor A_1” separates A_t from B_t: `a b=A_t`, but aM contains no B_t.
4. Right multiplication by b separates the remaining positive-index A/B or B/D pairs; right multiplication by ab separates B_0,D_0.

Different indices were already separated. These are actual generated context and factorization tests, not unrestricted arbitrary probes.

### 6.2 Coordinate necessity without a product assumption

Let E be ANY full-profile stable refinement of E0, possibly relational across input coordinates and varying independently by profile. At each active coordinate i, E determines every stage D_t of the finite monoid combined splitter:

* the initial observation is determined;
* right multiplication at i is an actual labelled unary identity graft at that input;
* left multiplication is an actual labelled unary identity above the whole, multiplying all active coordinates, after which coordinate i is inspected;
* transport swaps the actual channels;
* the actual cut with one unary identity at EACH input has factor labels `u_j v_j=x_j`. Projecting its full joint E-signature to the current monoid classes of u_i,v_i gives EXACTLY the monoid factorization signature of x_i. Every factorization of x_i extends to other coordinates by `u_j=x_j,v_j=e`.

Induction therefore forces E to distinguish both complete M_k channel labels at each active occurrence. There is no assumption that E itself is product-shaped. Since old data were already exact, E must be discrete over each old record. The discrete family is plainly stable under every actual permitted operation and relation. It is therefore the coarsest simultaneous refinement.

This supplies the positive optimality theorem, an effective output representation and a finite distinguishing schema valid for every full profile. It does not claim that earlier separate-repair stages have a uniform coordinatewise form. Full proof is `profile_schemata_theorem.md`, §4, with concrete identity-operation realizability established by `model_and_core_comparison.md`.

### 6.3 A judgment changed by the repair

In the unary slice A_t and B_t have the same initial observation. After the necessary tests isolate a, the declared joint query “does this operation admit a cut whose left factor is a?” is true of A_t and false of B_t. Forgetting that distinction corrupts the actual cut judgment.

For a genuinely branching two-active-input operation in M_4, compare source label vectors `(A_1,A_1)` and `(A_1,B_1)`. Even their unary C-repaired coordinate observations Q agree: both index vectors are (1,1). Group both leaves under ONE parent and require that parent's index to be 1 and both inner labels to have index 0. The feasible parent set for an A_1 output is `{A_1}`; for a B_1 output it is `{B_1}`. Thus the first source has a simultaneous witness and the second does not, despite both marginal tests separately succeeding. This is an explicit cut judgment requiring correlation BEYOND coordinatewise unary repair.

Independent finite calculation on the k=4, N=2 active-label fragment gives 38 C-only classes on rank-two tuples, not the 16 classes of Q²; simultaneous S/C gives all 100 tuples. These are finite certificates for that declared template fragment, not the proof of the arbitrary-N theorem. They directly reject the tempting but false coordinate-product shortcut. Product INDEPENDENCE BETWEEN THE TWO CHANNELS, used in §7.3, is a different statement and does not erase correlations between active occurrences WITHIN one channel.

## 7. Commutation: criterion, positive laws and scope

### 7.1 Exact structural matching criterion

The generic finite criterion in `repair_calculus.md`, §5, is stated on actual joint records. For deterministic contexts D and cut repair K=C(E), first distinguish sources by ALL generated D tests of K. For any pair still equivalent and any actual cut record at one source, require ONE cut record at the other source matching every factor under EVERY generated D test of K simultaneously. Reversing the sources is also required. Separate witnesses for separate tests do not satisfy this synchronized gate.

This gate is necessary and sufficient for `D(C(E))` to remain C-stable. The other order requires every generating context to preserve the classes of `C(D(E))`; an explicit context/cut rewriting law with a well-founded downward movement of pullbacks is a structural sufficient certificate. Together the two gates are equivalent to commutation at E by leastness. Concretely, assign each factor v its finite context-action vector `V_K(v)=(K(h(v)))_(h in D*)`. For each source and cut grouping, enumerate actual tuples `(a_i,b_ij)` satisfying `x_ij=a_i b_ij` and record the SINGLE whole vector tuple `(V_K(a),V_K(b_1),...,V_K(b_m))`. The synchronized gate compares these sets, with one a_i shared in every equation of its group. All entries are computed from the actual multiplication table and declared context templates, not inferred from independent marginal signatures. Applied for all admissible E they characterize global commutation. On finite certified systems the gates are effective: enumerate the finite semantic context closure and actual joint record signatures. They do not claim arbitrary unbounded old-profile systems admit a finite table without a schema proof.

In the selected model, the witness side of the gate is precisely the existence of SHARED parent multipliers satisfying all required class/context tests simultaneously. Thus this is a witnessed-decomposition matching criterion, not merely the notation `SC=CS`. The M_k example exhibits failure by an actual parent-factor/graft distinction. On an S-complete input E, this specializes to an especially direct criterion: S and C commute at E iff the computed joint cut-theory equivalence C(E) is preserved by every elementary actual context generator. For the singleton M_k slice these are left/right multiplication by a,b; the table entry `e Q b` but `ae not-Q ab` fails the criterion. For the finite-group coset class the shared-parent inverse construction below proves the joint cut equivalence already equals E, so every multiplication generator passes. These are explicit positive/negative instantiations, not only the abstract condition that two closure composites be stable.

### 7.2 Deterministic S/T law

The actual channel swap conjugates each elementary branchwise graft to the corresponding graft with swapped constants. Domains, full profiles and old data are carried by the frame action. Therefore every mixed deterministic word can be rewritten as transport-after-context and as context-after-transport. The generated observation languages agree, so S and T commute globally on typed partitions for this declared action.

### 7.3 Restricted C/T law, not a false global claim

At channel-product partitions P⊠Q, the actual fixed-skeleton cut fibres are Cartesian products of two nonempty channel fibres. Their class-tuple signatures factor, and equality is reflected by projection. Every finite elementary C stage therefore acts channelwise. For the infinite full-profile family, the descending omega-limit is stable: for each fixed source cut record the finite nonempty candidate-match sets are nested, so one matching record survives all stages. The limit preserves the channel product. Thus C acts channelwise on these partitions without assuming a finite profile normalizer; arbitrary within-channel correlations remain allowed. Starting at P⊠top, T gives P⊠P and

`C T(P⊠top)=C(P)⊠C(P)=T C(P⊠top)`.

This applies to the selected initial observation. It does NOT prove C/T commute at every correlated partition. Swap closure on P⊠Q involves `P∩Q`; relational cut repair need not preserve arbitrary meets. Equivariance alone is insufficient because different observations can require incompatible matching witnesses.

## 8. One-pass positive class with nontrivial compression

Replace M_k by a finite group G and choose a proper nontrivial normal subgroup J. Observe the first local channel modulo J. S and C do not refine that observation; T adds the second channel modulo J. The result has `[G:J]^(2r)` classes rather than `|G|^(2r)` and is already simultaneous-complete.

The nontrivial cut proof is joint: for equivalent sources x,x' and any actual grouped factorization `x_j=a_i b_j`, keep ONE parent representative a_i and set `b'_j=a_i^{-1}x'_j`. Normality ensures every child remains in the required coset, simultaneously across the whole group. The same argument works recursively for finite cut trees. Transport swaps the two identical quotient observations. This is a useful compressed positive repair, not three identity operators or recovery by fiat.

For a concrete test take G=C4 and J={0,2}; two-channel T increases information from one parity bit to two parity bits while continuing to forget both even shifts. It supplies an abstraction complete for S/C but not T and a nontrivial one-pass simultaneous result.

## 9. Stabilization, effectivity and necessary cost

For a genuinely closed finite typed system with n total elements and b initial blocks, the elementary combined splitter has at most n−b strict refinements; a complete cycle of saturated S/C/T with no change certifies stability. Fair iteration reaches the least common refinement. This is an imported height bound, not the entire I5 result. The principal infinite-profile family also has a UNIFORM effective bound: the simultaneous elementary splitter is discrete by `R(k)+4` rounds when all labelled unary identities are primitive elementary contexts, or by `R(k)+5` when the primitive elementary multiplier basis contains a,b in BOTH channels and right-ab is counted as two steps. First-channel generators plus swap alone would require separately counting conjugation and do not justify the same optional bound. The stagewise coordinate lemma proves this across EVERY exact old profile: one transport step exposes both channels, R(k) cut steps expose indices, then S/C/S isolates rows, constants and remaining pairs. Intermediate global partitions need not be product-shaped. This is an upper bound, not an exact combined-round count or an enumeration of infinitely many old guards; see `profile_schemata_theorem.md` §8.

In the selected unary M_k cut system, the exact elementary c-iteration has first index blocks `{0},{1},{2,...,t}`. From round r>=2 it isolates every index below `min(2^r,t)`, isolates t, and leaves the remaining finite interval as one block. Therefore the exact number of strict elementary-cut rounds is

`R(k)=max(2,ceil(log2(k−2)))`.

The threshold doubles because a residual/residual factorization first appears at index twice the current singleton cutoff. This is a genuine growing lower-bound family for the stated natural splitter. Saturated C and S can instead reach the discrete monoid after the schedule C,S,C,S; there is no claim of unbounded full-repair sweeps.

The simultaneous monoid repair requires 3k−2 classes from two initial blocks. On a rank-r full profile in the two-channel class, the optimum requires `(3k−2)^(2r)` classes and at least `ceil(log2((3k−2)^(2r)))` bits in an injective fixed-length encoding. These are information lower bounds, not physical sensor or optimal-runtime lower bounds.

An effective output schema simply retains the exact old record and complete ordered active-label tuple. To certify necessity, compute the finite monoid splitter on p=|L| labels: at most p−b0 strict combined rounds, with explicit multiplication/factor tables. A conservative implementation uses O(p^4) total table/word accesses with O(log p)-bit indices and O(p^3) bits of signature working memory. Charging O(log p) per indexed-word access yields the conservative O(p^4 log p) indexed-word bit charge; this is not an unsupported O(p^4) pure-bit runtime claim. Representation conventions are stated in `profile_schemata_theorem.md`. These are not succinct-input bounds. Finite label-template records through rank N are bounded by a constant-factor finite structural multiplier times `2^N p^(2N)`; actual old profiles are not enumerated. Arbitrary-depth validity comes from the local-syntax induction and coordinate necessity proof, not a bounded-depth test.

## 10. Modular local-to-global repair in the selected presentation class

`modular_repair_theorem.md` proves a concrete conservative comparison, not unrestricted I1. Local coefficient theories A and B share the nontrivial exact old graph/interface presentation. Their global comparison uses coefficients A×B, embeddings a↦(a,1), b↦(1,b), and the declared cross-channel interchange relation along each branch. Projection retractions preserve old/local operation equality; normal forms are the ordered pair of branch products. This is a comparison quotient with specified mixed equations, not an unproved categorical pushout.

For every actual common cut skeleton c and fixed global source (x,y),

`W_(A×B)(c,(x,y)) ≅ W_A(c,x) × W_B(c,y)`.

Each local cut lifts at that fixed global source by unit internal labels and source labels on the omitted channel's leaf edges. Thus local matching records glue over the SAME retained skeleton. Local optima combine into the global optimum when the initial observations decompose by channel, common structural data are exact, and any exchange transport respects the two local repaired observations. The proof of optimality projects an arbitrary global stable relation, takes its finite-chain equivalence closure and uses fixed-source cut lifting to show that the result is a local stable relation. Merely intersecting two generic shell outputs would not establish these facts.

The positive M_k² control gives both local channels the same H observation. The global optimum is their product and is exchange-stable. The failing control uses H only on A and an indiscrete B observation: independently repaired locals identify `(e,e)` with `(e,a)`, but actual exchange sends them to `(e,e)` and `(a,e)`, which the candidate separates. Thus the local combination is not T-complete. This is an all-k family with a real common graph/interface subtheory and an actual mixed transport, not a disjoint-signature example.

A stronger comparison family has local coefficients A×K and K×B over a nontrivial shared coefficient monoid K, global coefficients A×K×B, and observations retaining the complete K separator record. Actual cut witnesses are then a pullback over the SAME K-labelled cut record. Exact separator observation makes local matches glue, while fixed-source lifts and context lifts give optimality. This is an explicit checkable sufficient class, not a classification after forgetting separators.

There is also a sharper SAME-CUT failure, without an omitted transport generator, in `modular_repair_theorem.md` §8. At N=1, an explicitly tabulated eight-element transformation monoid K has two individually multiplication- and joint-cut-complete partitions P,Q. Their meet identifies sources 0 and 1, although source 0 has a cut `0=0·t` of combined factor classes `(D,{t})` and source 1 has none. P matches with `1=1·1`, Q with `1=1·e`: the local certificates choose incompatible actual shared second factors. Adding private factors A,B gives genuine local extensions A×K and K×B; retaining K exactly restores gluing. The N=1 restriction is essential: the coordinatewise local partitions are NOT claimed complete with several active leaves. This failure concerns the same joint cut, not two unrelated closures.

For retained refinement certificates, `modular_repair_theorem.md` §9 normalizes actual occurrence-indexed coefficient forests using the new unary D relations and cross-channel sorting. A global certificate consists of the pinned common-spine certificate plus equality of path-products at every final active occurrence. It holds iff both projections do, and compatible local coefficient arrays pair entrywise over the SAME forest. Recuts, grafts and the declared interface transport commute with this pairing. The old-source dependency is precisely the scope in `model_and_core_comparison.md` §7, not a blanket assertion that the old seven-rule theorem proves the new coefficient relations.

These theorems determine when the selected local repairs combine and give positive/failing controls. They do NOT discharge the unrestricted original I1 rewriting/refinement-amalgamation theorem, arbitrary interface identifications, or forgotten-skeleton gluing. Only the explicit coefficient/graph witness and cut/refinement diagrams represented here are claimed.

## 11. Baseline comparison and novelty boundary

`baseline_comparison.md` audits primary sources. Giacobazzi–Ranzato–Scozzari already supply complete-shell/core theory under precise hypotheses, including reduced-product modularity; Ranzato–Tapparo and coalgebraic partition refinement supply generic stabilization/minimization infrastructure; Turi–Plotkin supply syntax/behavior compatibility baselines under their actual hypotheses. None is credited to this package as new.

The residual supplied here is the particular graph-linked witness enrichment and relative presentation; exact joint shared-parent cut semantics; the concrete M_k noncommutation/discreteness and elementary-round family; the all-full-profile coordinate necessity argument; actual channel transport and its limited commutation claims; and fixed-source cut gluing in the selected conservative comparison. This is a significance statement about what was proved, not a literature-priority claim.

The earlier fixed-generated-language permission minimizer and no-coarsest-fullness-boundary counterexample remain useful inputs. They do not replace this simultaneous operation package. Here an optimum EXISTS in the all-typed-partition class. No claim is made about a minimum physical encoding, arbitrary boundary lifting, or a product-only abstraction class. If a smaller representation class is requested later, its closure/enlargement is a new explicit question rather than an implicit restriction of this theorem.

## 12. Obligation ledger and current acceptance state

| I5 requirement | Author result / boundary |
|---|---|
| Specified starting abstraction | Exact old data + first-local-channel H membership, §§1–3 |
| Least refinement for S/C/T | Explicit global optimum among all typed partitions, §6 |
| Effective extra information | Actual complete active-label tuple; shared-parent cut records, §§4,6,9 |
| Three defined repairs | Input-relative saturated S/C/T with exact Boolean joint signatures, §3 |
| Complete unbounded basis/schemata | Actual local graph-label templates + syntax induction + finite coordinate necessity; no generic profile-erasure assumption, §§4,6 |
| Full profiles as sorts | Retained throughout; old witness data additionally exact, §2 |
| Structural commutation criterion | Synchronized actual cut witnesses + context gate; global S/T, restricted C/T and actual S/C failure, §7 |
| Unbounded noncommuting family | All k>=4 with actual fixed-profile graft/cut obstruction, §5 |
| Stabilization upper/necessity | Finite closed-system height bound; exact logarithmic elementary-C rounds; exact retained-state lower bound, §9 |
| One-pass positive control | Proper finite-group quotient with nontrivial T repair, §8 |
| Complete for one operation not others | E0 S-complete but not C/T; group control S/C-complete but not T |
| Changed application judgment | Actual unary left-a cut and branching shared-parent query, §6.3 |
| I1 local/global control | Selected conservative comparison and fixed-source gluing; asymmetric exchange failure, §10 |
| Optimal-domain failure/enlargement branch | Not invoked: optimum exists in selected admitted class |
| P and C evidence | Analytic proofs, independent proof/coverage reviews, and separately reproduced finite certificates with declared limits |

**Scope of the reviewed result.** The original I5 outputs are supplied for this graph-linked witness enrichment and Boolean joint-cut observation doctrine, relative to the precisely named original graph-spine presentation. This does not discharge unrestricted I1/I4 or the whole contract. `proof_review.md` records the non-author mathematical review and corrected issues; the coverage and verification reports record their separate verdicts and ranges. Agent-based review is not external human certification or a new Lean proof, and correlated-model limitations remain. Finite calculations support but do not replace the unbounded arguments.

## 13. Artifact map

* `concrete_model_gate.md`: independently approved scope and chosen guarantee.
* `model_and_core_comparison.md`: model laws, relative presentation, old comparison, transport, singleton lemma.
* `monoid_repair_theorem.md`: analytic M_k theorem, discreteness and exact elementary rounds.
* `profile_schemata_theorem.md`: guarded local coverage, all-profile coordinate necessity, effective costs and group positive control.
* `repair_calculus.md`: finite typed least repair and synchronized matching criteria.
* `modular_repair_theorem.md`: conservative comparison, cut-fibre pullback, optimum and failure controls.
* `baseline_comparison.md`: primary-source hypothesis audit and non-novel baseline infrastructure.
* Independent proof, obligation-coverage and reproduction reports: reviewed scope, corrections and verification limits. Exploratory framing notes are not needed to use the theorem package.

The bundled content-hash manifest pins the delivered proof, dependency and review files. Verification reports identify their executable inputs and exact tested ranges; mathematical claims outside those finite ranges rest on the analytic proofs.
