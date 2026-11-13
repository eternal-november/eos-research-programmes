# Prior-art and contribution audit: the actual original mixed calculus

29 October 2026. Scope/significance review of the four current proof candidates; not an independent verification of every proof or a claim of literature exhaustiveness.

## Plain-language verdict

The most useful advance is that we now know a proposed bridge **cannot hold as originally hoped**: adding interface changes and composition to the old syntax does not produce all the components in the larger span model. More strongly, we now characterize exactly which horizontal objects the ordinary envelope does generate: all graph-free spans, and precisely those graph-bearing spans whose witness-count matrices factor through an old interface. The proof supplies a compiler from such a factorization. We also have an exact answer for one natural family of information-forgetting rules, including a proof that completing the calculus does not secretly forget more about the old witnesses.

These are meaningful programme advances, not a new general mathematical mechanism. The proofs use familiar algebra, factorization rank, universal presentations, and groupoid descent. The remaining substantial task is to supply and justify the missing generators and cell equations, rather than relabel the larger semantic model as the original calculus. The optional groupoid repair changes what counts as an interface and as exact recovery; it must not be counted as solving the original set-valued transport problem.

## 1. Exact contribution ledger

| Candidate | What it contributes here | What it does not establish |
|---|---|---|
| `C5_Fixed_Endpoint_Kernel_Classification.md` | Derives partition rigidity from actual fixed endpoints; classifies graph-indexed scalar kernels as one unit-subgroup orbit relation on nonempty graphs and equality on empty graphs; gives original-generator equations. | Classification of arbitrary profile-dependent kernels; exactness of every cut comparison; a general new theorem about monoid quotients. |
| `Original_Envelope_Quotient_Bridge.md` | Uses the original presentation and a graded separating model to show the stated scalar equations add no unintended old equalities under all chosen completion constructors. | Fullness of old cells inside the envelope; classification of new cells; a global scalar normal form on formal composite branches. |
| `Generation_Boundary.md` | Classifies the entire ordinary horizontal essential image using nonnegative integer factorization rank, gives a witness-preserving compiler, and proves non-generation plus a sufficient carrier extension. | Non-fullness on old profiles; cell generation/completeness after extension; uniqueness/minimality of the carrier schema. |
| `KernelPair_Provenance_Repair.md` | Specializes kernel-pair groupoid descent while retaining original witness provenance and identifying the exact support-coverage condition. | A repair within the original discrete-interface doctrine; arbitrary missing-value recovery; generation from the old seven rules. |

The strongest new structural result is the third row: an exact image criterion, not only an obstruction. Its necessity depends on the original grammar, and its converse constructs a term from a factorization rather than assuming generation. Graphs supply the existing occurrence-sensitive word grading. This remains a horizontal-object theorem for the ordinary envelope, not a converse for the smaller virtual grammar or a theorem about cells.

## 2. Strong standard baselines

### 2.1 Scalar kernels and free presentation quotients

The algebraic core is elementary: saturation gives a class of the unit whose elements must admit inverses, and all classes are its multiplicative orbits. No novelty should be claimed for unit groups or orbit congruences. The actual programme-specific burden is proving that singleton refinements force the same subgroup at every nonempty graph, that nullary refinement forces equality on empty graphs, and that these equations follow from the **old** D/graph-cut rules.

Likewise, adding equations before or after a free presented construction is standard universal-property reasoning. In the present proof, the important extra assertion is **old conservativity**, which does not follow merely from this commuting diagram. It needs the explicit separating model and its conserved vertex grade. Closing the congruence under inverse-factor constructors is essential to retaining the chosen equipment axioms.

The earlier general CRT/reconstruction criterion remains a separate, largely classical layer. This package does not make CRT itself new; it supplies an actual original-calculus family to which fixed-endpoint lifting applies.

### 2.2 Integer factorization rank: a standard invariant, an exact grammar classifier

For fixed endpoints, a finite span is determined up to isomorphism by its matrix of witness multiplicities. Pullback composition multiplies these matrices over the nonnegative integers. The revised criterion is:

- empty graph word: every finite span is generated;
- nonempty graph word: a span is generated exactly when its nonnegative integer factorization rank is at most `b=max_A |F(A)|`.

Factor rank and its product inequality are standard. [Johnson–Kambites, *Green’s J-order and the rank of tropical matrices*, Example 8.2 and Corollary 8.3](https://arxiv.org/pdf/1102.2707), define factor rank over arbitrary commutative semirings and prove its monotonicity under multiplication. Despite the paper's tropical title, these statements are for general commutative semirings. [Gouveia–Wiebe, *Matrices of nonnegative integer rank two*, Introduction](https://arxiv.org/html/2602.05957v2), explicitly identifies nonnegative integer rank as this factorization-rank specialization. Thus neither the rank notion nor the bottleneck inequality is a new mechanism.

The specific contribution is the equivalence with the **actual original horizontal grammar**. Necessity follows by tracing any old graph-bearing leaf through restrictions and compositions, retaining a factorization through its bounded interface. Sufficiency realizes the two integer factors as graph-free spans around a sequence of old identity-interface graph components. This both detects non-generation and compiles a successful factorization into a generated horizontal. It is an image theorem, not a syntactic normal form or a lift of every semantic isomorphism.

Boolean rectangle rank is only the weaker support shadow. Compare [DeSantis et al., *Factorization of Binary Matrices*](https://arxiv.org/html/2012.10496v2) and [Haviv–Parnas, *On the Binary and Boolean Rank of Regular Matrices*](https://arxiv.org/abs/2203.13073). The matrix `[[1,1],[1,2]]` has Boolean support rank one but integer factorization rank two: the duplicate witness matters. At `b=1` its graph-bearing span is not generated although the all-ones span is. The revised criterion therefore genuinely retains multiplicity rather than silently turning witnesses into relations.

**Checking versus search.** Given explicit binary-encoded nonnegative integer matrices P,Q,X, checking dimensions, the width bound, and `PQ=X` takes polynomial bit time in their combined encoding size by ordinary exact arithmetic. This is a claim about a supplied horizontal-generation certificate, not an efficient factorization search, minimal-width computation, or verification of arbitrary cell equations. The compiler's explicit apex sets may have size proportional to the sums of matrix entries, exponentially larger than their binary encoding. No polynomial-time full syntactic compilation in that compressed input size follows. No NP-hardness or completeness assertion is made here.

### 2.3 Spans, companions/conjoints, and the missing cell theorem

Factoring a span through its apex using a conjoint and companion is standard. [Dawson–Paré–Pronk, *Universal properties of Span*](https://tac.mta.ca/tac/volumes/13/4/13-04abs.html) is a primary universal-property baseline; its abstract describes two related universal properties. No stronger precise theorem from that paper is used here.

A particularly sharp comparison is [Aleiferi, *Cartesian Double Categories with an Emphasis on Characterizing Spans*](https://arxiv.org/pdf/1809.06940), Chapter 5. Theorem 5.3.2 characterizes spans via Cartesian, fibrant, unit-pure structure and strong Eilenberg–Moore objects, equivalently an appropriate canonical comparison with spans. Its proof uses strong tabulators to obtain horizontal essential surjectivity and then separately proves fullness and faithfulness using their universal property. Section 5.2 identifies the Beck–Chevalley condition needed for the comparison.

This is precisely why our carrier formula does not supply the missing cell theorem. It gives objects of the form conjoint–carrier–companion, but does not automatically supply carrier naturality, sliding equations, all maps of apexes, or their interaction with graph cuts and scalars. Nor do generic equipment axioms assert all the extra tabulation/Cartesian hypotheses of the span characterization. The graph-bearing carrier is an additional generator, not an ordinary graph-free unit in disguise.

### 2.4 Kernel-pair groupoids: directly standard descent

The appendix's central mechanism is already explicit in [*Toward the effective 2-topos*, Lemma 3](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/toward-the-effective-2topos/00CF42DEA9BF2A045D67898232919258): a groupoid mapping to a discrete object is an equivalence exactly when its object map is epic and its arrows form the kernel pair; a section supplies a strong inverse. Our finite-set instance is immediate. Restricting to the image gives the support condition in the nonsurjective case.

Retaining the original witness as a separate provenance coordinate prevents unrelated witnesses from being merged, and is a valuable modelling choice. It is not a new descent mechanism. Replacing discrete lifts by a groupoid with new arrows changes the doctrine. In particular equivalence of groupoids at the nullary diagonal is not a bijection of the original sets.

## 3. What was already in the dossier

The audit inventory gives the exact source paths. The following must be credited as dependencies, not counted again:

- `Conservative_Equipment_Envelope.md`: original free chosen virtual/ordinary envelopes, universal interpretation categories, and the graph-word × span × scalar separating model. Its distinction between an old empty-graph letter and the fresh empty word is crucial to the new rank proof.
- `GraphDependent_Quotient_and_Cut_Memory.md`: activated coefficient forgetting, induced-upward activation criterion, and original full-profile conservation. The new scalar classification addresses a different kernel family and the stronger fixed-actual-endpoint lifting demand.
- `Global_Cut_Repair.md`: coherent laminar repair, scalar-one interval records, and the need for actual comparison-fibre bijections, including nullary diagonals. Repeating those phenomena is not a new result.
- `TerminalRestriction_NoGo.md`: restriction can propagate seemingly local identifications back to original data. The new scalar bridge is a positive family escaping that obstruction, not a repeal of it.
- `Extended_Local_Presentation.md`: a larger syntax naming arbitrary finite-span data. Its seven schemes are not the seven original C5 equations. Importing its completeness is exactly the invalid shortcut the generation boundary now excludes.

## 4. Remaining hard target and contract consequences

A substantive continuation is a **relative presentation theorem for a precisely stated carrier extension**, including cell generators, equations, and a conservative comparison with the old calculus. It must prove, rather than assume, that every intended cell is generated and that all semantic equalities follow from the proposed rules. Nullary common boundary maps and noninvertible changes must appear in the proof. Alternatively, further invariants may prove that even a proposed extension remains insufficient.

The other open direction is classification beyond graph-indexed scalar kernels: profile-dependent and coefficient-map quotients, with actual-endpoint lifting and cut recoverability distinguished. The current partition obstruction constrains this problem but does not solve it.

No complete discharge of original reconstruction/recoverability/2-Segal obligations follows from this package alone. In particular, horizontal generation, equality reflection on old cells, fullness on new cells, and exact transport of cut witnesses are four different assertions. A groupoid-valued replacement may be a useful companion doctrine, but cannot silently discharge the original discrete assertion.

**Recommended contribution language:** “An exact original-calculus scalar classification and conservative completion theorem, together with an exact integer-factorization characterization of the ordinary horizontal image, a witness-preserving compiler, and an explicit object-level extension.” Avoid “complete classification of admissible quotients,” “full mixed-calculus presentation solved,” or “noninvertible cut recovery established without changing the framework.”
