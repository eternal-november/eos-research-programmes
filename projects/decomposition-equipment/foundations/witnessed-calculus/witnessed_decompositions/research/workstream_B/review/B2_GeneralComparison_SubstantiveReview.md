# B2 arbitrary semantic comparison: independent P-slice review

**Verdict: PASS for the general P arguments in §§1–5 and §7.**
The quotient conclusions explained in §6 are correct under their stated
associativity/profile-preservation assumptions, but the separately promised
principal certificate is not certified by this review. No whole-B2 or Lean
acceptance is implied.

Reviewer: `/root/review_refinement_target_depth`, separate from author
`/root/prove_refinement_obligations`. Review conducted 24 October 2026,
22:46–22:49 UTC. This is agent-managed non-author mathematical review, with
shared-model limitations and no external human certification. No source edits
or proof authorship by this reviewer occurred.

## Reviewed hashes and dependencies

Project root:
`/workspace/shared/witnessed_B_20261024/witnessed_decompositions`.

- `research/CompletionContract.md`:
  `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
- Unchanged `research/workstream_B/B1_B2_Targets.md`:
  `37912984dfcd045bb504e738823f8194e933975d5d94e043da50253cf94c8092`.
- `research/workstream_B/B2_GeneralComparison.md`:
  `5df666c820c4876b9beed8529cdbb5d3968ff72763e3162287f14a5a1afaaea4`.
- Already separately reviewed B1 P dependency:
  `bf1cf8ed1dca187706a15cb8b80f897f3b4465da7394e9211ab89a0f2a1067da`.

The accepted A1/A2 source was inspected for the actual APIs used: `Calc` has
profile-preserving occurrence substitution and the two unit/associativity laws;
`slotExpand` and `slotExpand_assoc` preserve typed nested occurrences;
`profileSubstitutionEquiv` and `profileGraft_eq_graft` link actual free-calculus
families and structural forests; `Tree.extend` is a strict interpretation.
Relevant unchanged source hashes include:

| File | SHA256 |
| --- | --- |
| `Calculus.lean` | `7f47c010035f6676aab3ab782b0446c2d93509e41a76ac23fda09454fedfcf5c` |
| `PathOccurrences.lean` | `7501e40ef86071de4ea176ad72dc67c9895ee607b2cf77d4c194545bb0d392bc` |
| `TreeOccurrences.lean` | `bf0e5d53cb4a09072b2921d584315d2ba9e0e5eae61881896a183fe650cf85b1` |
| `FreeCalculus.lean` | `294ab03493698787c35cfc104b6b6c79748c61a32e2440c55ce9e7fadfefe16e` |
| `FreeExtension.lean` | `ae5991a75daa8e0ded0e796811223823837c3d5cd482475559e085f88f85c543` |

This is not a new reproduction of A1/A2 acceptance or a check of the still-in-
progress B Lean files. The P argument is assessed at its exact stated generality.

## 1. Actual semantic tuples and category laws

The object class is all operations at a fixed whole, not only interpreted
trees. The arrow type retains the entire tuple at the original profile slots
and only treats its endpoint equality as proof-irrelevant. Each entry determines
its complete profile; therefore different segmentations cannot be erased by
equality of the total substituted operation. No cancellation or injectivity
hypothesis has been smuggled into the target class.

I reconstructed composition from the accepted profile law: the endpoint
`a[b]=a'` identifies `profile(a')` with the ordered concatenation of the
profiles of the `b_i`. The canonical slot equivalence pulls each second tuple
entry back to a unique typed pair `(i,j)`. Substitution into each `b_i` is thus
well typed, and the outer associativity equation proves its advertised endpoint.
This is a construction of a tuple, not a quotient by common endpoints.

The category proofs compare entries rather than only resulting operations.
The right unit is the target right unit inside each `b_i`. The left unit uses
the singleton block for each original position before the target left unit.
Associativity uses the same typed triple occurrence on both parenthesizations
and then the target operation associativity inside each original entry.
Dependent function extensionality and proof irrelevance finish tuple equality.
These are exactly the laws available from `Calc`, not additional target fields.

Nullary blocks are not a missing case. If one `b_i` has empty profile, its
second-layer subtuple is uniquely empty and `b_i[()] = b_i` by the right unit
law. Other entries retain their separate occurrences; no fallback occurrence
is inserted into the missing block. If the outer profile is empty, the whole
tuple is empty and the same unit law applies. Unary/repeated-color positions
are likewise ordinary distinct slots, not labels used as keys.

The equality transports depend only on propositions expressing the full
profile equalities. Within the accepted extensional Lean/set-level convention,
proof irrelevance and equality elimination make the two composite transports
agree. There is no tacit demand for extra higher coherence data on `Calc`.

## 2. Functoriality for arbitrary strict morphisms

The proposed map is well defined on every semantic arrow. A strict map preserves
the whole profile and each entry's profile, so it preserves both the outer
index set and each inner segmentation. Substitution preservation gives the
mapped endpoint equation. Identity preservation is entrywise. Composition
preservation is the equation `H(b_i[d_ij]) = H(b_i)[H(d_ij)]` at every original
slot with the same pair correspondence. Thus the proof does not infer functor
laws merely from equal evaluated endpoints.

Identity and composite strict morphisms act respectively as the identity and
ordinary composition on every object and tuple entry. The stated profile
transports coincide by equality transitivity/proof irrelevance. The result is
valid across the accepted independent operation universes; it imposes no finite
signature, decidable equality, presentation, or normalization restriction.

The free-source comparison is also substantive. A1's family/forest equivalence
gives inverse maps on the retained arrow data and its graft theorem gives the
same endpoint. Identities correspond. B1's leafwise composition equation and
the A1 profile/leaf square identify both compositions entrywise. Hence this is
an actual identity-on-objects category isomorphism, not an unsupported reuse of
the same category name. Composing it with `Ref(Tree.extend)` gives the desired
raw evaluation functor.

## 3. Exact strength of the comparison hypotheses

The equality-reflection criterion is valid. Componentwise operation injectivity
reflects object equality in each fixed whole. For two mapped arrows between
fixed source objects, transport their equal image tuples back along the same
profile equality; componentwise injectivity then reflects every entry equality.
No target cancellation is involved.

The raw-source caveat is crucial and correctly proved: each raw hom-set is a
subsingleton, so every raw-source functor is categorically faithful regardless
of what it forgets on objects. The dossier does not advertise this automatic
property as witness recovery or fullness.

For lifting, the proof uses two logically distinct hypotheses in the correct
places. A supplied exact-profile tuple `x_i` lifting the target entries gives
`H(a[x_i]) = H(a')` by strictness and the semantic endpoint. Injectivity at the
fixed whole then yields the missing source endpoint equation. It would be
incorrect to omit this last injectivity condition or to assume that entrywise
surjectivity already establishes the endpoint; the dossier does neither.

Existence does not silently imply uniqueness for a general source calculus.
Raw uniqueness uses B1 thinness, while general-source uniqueness separately uses
entrywise injectivity. If lifts are individually existential, the finite-index
choice step is exposed rather than hidden. Profile preservation indeed makes
the exact-profile condition follow from equality of mapped total operations,
but retaining it in the statement usefully prevents an output-only lift.

The uniform hypotheses yield fullness on the corresponding image-object pairs,
and hence refinement-existence reflection there. Bijectivity on every operation
fibre gives both total-operation injectivity and surjectivity because profiles
are preserved; therefore the stated raw special case is sound. The strict
calculus-isomorphism consequence follows more directly by applying `Ref` to
the given strict inverse. None of this is a necessary-and-sufficient
classification or a B3 categorical-quotient theorem.

## 4. Quotient explanation and evidence boundary

The mathematical mechanism described in §6 is correct: if actual associativity
identifies `L=μ[μ,1]` and `R=μ[1,μ]`, then the tuples `([μ],[1])` and
`([1],[μ])` give parallel semantic arrows to `[L]`. Their first entries cannot
be equal because their profiles have lengths two and one and the quotient is
parallel. The unique raw arrow `μ→L` is the left expansion; its image is not
the right tuple. Uniqueness, rather than failure of one representative attempt,
excludes all possible raw lifts. This explains failure of fullness even though
individual quotient entries have representatives.

At review time, the cited file `B2_QuotientCertificate.md` was not present. The
author was notified directly. Consequently this review does not certify its
promised actual A3 instantiation, nonconstant witness statistic, mixed-interface
embedding, four-leaf coverage, or executable checks. The above verification is
of the general comparison mechanism under its stated inputs, not an assertion
that this separate dependency has already been delivered. Its absence is an
open example-evidence gate, not a counterexample to §§1–5.

## 5. Profile-typed negative control

The control in §7 is a lawful target, not an untyped singleton. For every fixed
whole its operations are exactly the paths with the same endpoints, profile is
identity, unit is the singleton whole edge, and substitution is typed ordered
path expansion. Both units and associativity follow from the already accepted
path expansion laws, including empty loop paths. Different wholes remain
separate indexed fibres even when their path types coincide.

Taking a raw tree's frontier is strict by the A1 frontier/graft laws. Where the
signature provides distinct parallel unary witnesses, their corollas have equal
frontier image while remaining distinct raw trees. Thus this genuinely forgets
witnesses but still induces a technically faithful raw-source functor. It
correctly functions only as a negative control, not the principal nonthin
witness-retaining certificate.

## Final verdict and outstanding gates

The general mathematical comparison is complete at the stated P level; no
unresolved correctness defect or target weakening was found. It has the
arbitrary-target and occurrence-sensitive strength required by the frozen
B2-S/F general comparison, rather than a selected-model shortcut. Its standard
infrastructure status is stated honestly and carries no new-novelty claim.

The mandatory L construction/functor laws cannot be replaced by this prose
verdict. New Lean declarations and their exact hashes, axiom closures, fresh
builds, and independent example review remain required. B1/B2 acceptance and
the separate B2-Q principal certificate remain outside this verdict.
