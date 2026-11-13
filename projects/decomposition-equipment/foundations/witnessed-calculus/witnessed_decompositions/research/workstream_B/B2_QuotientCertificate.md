# B2: a typed associative quotient with genuinely parallel refinement tuples

Contract v0.1, SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
This is the B2-Q certificate under the independently approved target
`B1_B2_Targets.md` (SHA256
`37912984dfcd045bb504e738823f8194e933975d5d94e043da50253cf94c8092`).
It does not construct or identify a categorical quotient of raw refinements;
B3/B4 and Workstream C are not activated. This is standard presentation and
refinement infrastructure, not a novelty claim or an integrated-bundle claim.

## 1. The parameterized presentation is explicit and nondegenerate

Let the interface set be **Nat**. For every ordered pair `(a,b)` there is one
component `c_ab : a→b`. These are endpoint-typed components: `c_01`, `c_11`,
and `c_12` are different even though the edge-carrier types each contain one
value. For every triple `(a,b,c)` supply a primitive binary witness

    μ_abc : (c_ab,c_bc) → c_ac.

For every pair `(a,b)` supply distinct primitive unary witnesses `red_ab` and
`blue_ab` on `c_ab`. For every `a` supply a designated nullary witness `zero_a`
with output `c_aa`. These are all generators of `RefinementExamples.S`.
The identity is the vertex-free leaf, not any of these unary/nullary witnesses.

For every quadruple `(a,b,c,d)` declare exactly the equation

    μ_acd[μ_abc,id_cd] = μ_abd[id_ab,μ_bcd].                 (A_abcd)

Both sides have precisely the ordered profile `(c_ab,c_bc,c_cd)` and output
`c_ad`; hence each is a legitimate parallel A3 declaration. The family has
unbounded interface parameters, and its substitution closure applies at
arbitrary finite depth, with arbitrary independently supplied replacement
frontiers. It is not a pair manually identified in a separate datatype.

`equations` is this inductive family of declarations.
`M = Presentation.quotient equations` is the **actual accepted A3 quotient** by
the least parallel substitution congruence `Presentation.Derives`. Its strict
map `projection` is A3's projection. No selected semantic kernel defines this
equality. A3 gives

    projection(t)=projection(u) iff Derives(S,equations,t,u).

All calculations below use this map and its proved strict substitution law.

### A retained witness distinguishes this from an indiscrete semantics

Assign weight 1 to each `red` generator and 0 to every other generator. A tree's
weight is the sum over its primitive vertices. Both sides of every `(A_abcd)`
have weight 0. A3's proved `Presentation.derives_weight` therefore implies,
for *every* pair of parallel trees in this presentation,

    projection(t)=projection(u) ⇒ redCount(t)=redCount(u).

In particular `projection(red_ab) ≠ projection(blue_ab)` for all `a,b`, because
the counts are 1 and 0. The same distinction survives the mixed-interface
context below. The declarations are nonempty and nontrivial, but do not collapse
all witnesses. This invariant supplies a sound separator, not a claimed complete
classification of the quotient.

## 2. Equal evaluated objects and unequal raw trees

Fix the loop `x=c_11`, write `μ=μ_111`, and let

    T = μ[id,id],    L = μ[μ,id],    R = μ[id,μ].

The source `T` has two distinct leaf occurrences, both literally of component
`x`. The trees `L` and `R` have the same three-leaf typed frontier but different
planar shapes. For example, the first child of the root in `L` is internal,
whereas that in `R` is a leaf. The recursive leaf-retaining `shape` function
makes this a formal constructor discrimination. Counting generators or recording
only their preorder list would *not* discriminate this repeated-generator case.
Thus `L≠R` in the raw syntax.

The declaration `(A_1111)` proves `projection(L)=projection(R)`. Hence the
interpretation is not injective on objects. There is no assumption here that
associativity holds in raw syntax.

## 3. Actual nonthin semantic refinements

Let `a=projection(T)` and `b=projection(L)=projection(R)`. In the semantic
refinement category the following are two arrows `a→b`:

    f = (projection(μ), projection(id_x)),
    g = (projection(id_x), projection(μ)).

Their endpoint equations are precisely the strict projection images of the two
raw graft calculations, followed for `g` by the declared quotient equality.
They are **tuples**, not proofs of mere reachability. Their entries remember
both their operation values and their separate full typed input profiles.
The first entry of `f` has profile `(x,x)` of length 2; the first entry of `g`
has profile `(x)` of length 1. Equality of tuples would imply equality of these
first operations, hence equality of their profiles, hence `2=1`. Therefore
`f≠g`. The semantic hom is genuinely not a subsingleton.

Nothing about this argument depends on choosing a representative of the final
quotient object: the entries themselves are quotient operations and their
profiles descend along A3 parallelism. Nor are the two arrows different
chronologies of the same raw forest. They expand different original leaf slots.

### The raw comparison is thin but not full

There is a raw arrow `T→L` with forest `(μ,id)` and a raw arrow `T→R` with forest
`(id,μ)`. These are *different target pairs*. Each fixed raw hom is subsingleton
by B1 unique forest recovery.

Suppose the semantic arrow `g:a→b` lifted to a raw arrow with the **fixed** raw
source `T` and target `L`. Let its forest be `h`. Since `T[h]=L=T[(μ,id)]`, B1
injectivity of grafting at fixed source forces `h=(μ,id)`. The A1
profile/structural forest equivalence respects this equality. Applying the
projection entrywise would then yield `f=g`, contradicting the profile-length
argument. Thus this arrow has no raw lift to the fixed raw target.

This is exactly nonfullness for the comparison on that source/target hom. It
is not a contradiction to automatic categorical faithfulness from a thin raw
category. Every raw-source functor is faithful on its fixed hom sets; that
vacuous property cannot recover distinct presentation objects or supply missing
semantic arrows.

The sufficient comparison hypotheses elsewhere in B2 therefore have a real
boundary here. A3 projection provides exact-profile representatives for every
quotient tuple entry, but **fixed-output object injectivity fails** (`L≠R` with
equal images). Entrywise liftability alone cannot force the raw endpoint to be
`L` rather than `R`.

## 4. The phenomenon is present in genuinely mixed-interface contexts

Define the typed context

    C(t) = μ_012[id_01, μ_112[t,id_12]],     output(t) = x.

More precisely `t` is an operation with whole `c_11`; its profile is allowed to
vary. The context retains all surrounding generator witnesses and the two
surrounding edges. Its interfaces include three distinct values `0,1,2`.

The raw source `C(T)` has four ordered leaves

    (c_01, x, x, c_12).

The two raw targets `C(L)` and `C(R)` have five ordered leaves

    (c_01, x, x, x, c_12).

They are genuinely nested trees and are unequal by the same retained-shape
separator. Applying A3 substitution congruence (equivalently, the strict
projection law twice) to `projection(L)=projection(R)` proves their evaluations
equal. They are not equated merely because their frontiers coincide.

The two arrows out of `projection(C(T))` have the explicit original-slot tuples

    F = (id_01, projection(μ), id_x, id_12),
    G = (id_01, id_x, projection(μ), id_12).

The displayed identities denote the corresponding quotient identities.
The Lean definitions obtain the profile families through the exact A1 inverse
`profileSubstitutionEquiv` of the displayed structural forests, so they use the
actual ordered frontier occurrences, not repeated-label lookup. Evaluation of
slot 1 yields the same `2≠1` separator as above, proving `F≠G`.
A fixed raw target `C(L)` again forces the unique left forest, so the right
semantic arrow has no fixed-target raw lift. This is the principal mixed
certificate, not an isolated one-object sanity check.

The red-count invariant also distinguishes `C(red_11)` from `C(blue_11)` after
evaluation, showing the contextual certificate does not erase all witness data.

## 5. Genuine composition and nullary behavior

From `projection(L)`, refine its first of three current leaves by `red_11` and
leave the other two unchanged. Denote that arrow by `r` and the resulting object
by `d`. Its endpoint is the image of a genuine raw simultaneous graft. The
red-count changes from 0 to 1, so `d≠projection(L)`: this is not an identity-only
test. The supplied `leftThenRedArrow` and `rightThenRedArrow` are the actual
semantic category composites `f;r` and `g;r`, both with endpoint `d`.

The general B2 tuple composition theorem splits the three-position second
forest according to the original tuple segmentation. For `f`, the first two
replacement entries form the new first component and the third is the second
component. For `g`, only the first entry forms the new first component, and the
last two form the second. Consequently these composites still have first-entry
profile lengths 2 and 1. The finite checker independently verifies this and all
other unary second-layer choices, including identity, red, and blue.

A nullary first replacement `(zero_1,id_x)` gives a genuine semantic arrow from
`projection(T)` to the image of `μ[zero_1,id_x]`. Its final profile has length 1,
not 2: the first original occurrence contributes an empty frontier, while the
existing binary vertex remains. In fact the binary-vertex count, also preserved
by every associativity declaration, proves this target differs from the identity
even though both have singleton frontier. There is no assertion that zero is a unit or
that arbitrary nullary substitutions preserve distinctions/cancellation. The
finite composition tests explicitly include nullary segments, including zero-
length slices in the second-layer split.

## 6. Finite independent evidence and its strict boundary

`research/workstream_B/examples/check_semantic_refinements.py` (project-root-relative) defines typed trees and an independent
full-profile additive witness-statistic target. An operation in that target
retains its output, complete ordered typed input profile, and counts of binary,
red, blue and zero witnesses. Identity has a singleton profile and zero counts;
substitution concatenates profiles and adds counts. For arbitrary such tuples,
unit laws follow from singleton concatenation and adding zero. Associativity
follows from associativity of ordered concatenation and addition, with the
second-layer entries split by each first-layer profile length. Thus this is a
lawful (nonterminal) model of every `(A_abcd)`; each declaration has the same
profile and two binary vertices on both sides.

This target is *not* asserted to be the exact A3 quotient: for example it may
forget where unary decorations occur. It is used only for independent finite
regression, never as a definition or completeness certificate for generated
congruence. The actual quotient claims are the Lean declarations above.

The finite domain is interfaces `{0,1,2}`, all 81 typed associativity quadruples,
and five replacements at each loop occurrence: identity, red, blue, binary, and
zero. The checker verifies:

* 81 distinct-tree/equal-model associativity instances;
* three loop parallel-arrow pairs;
* 750 two-layer tuple-composition equalities;
* 375 three-layer tuple-composition equalities;
* 183 nullary-containing second layers;
* the mixed four-leaf/five-leaf certificate;
* red/blue separation in the witness-retaining statistic target;
* rejection of a family with the wrong output component at one original slot.

The explicit negative-control map retains the **complete typed profile and
whole**, but discards all internal witnesses. It equates red and blue. This
shows that preserving profiles, or exhibiting equal evaluations of grouped
trees, does not by itself certify witness recovery. It is not offered as the
principal semantic certificate.

## 7. Formal declaration inventory and trust boundary

Source: `WitnessedDecompositions/RefinementExamples.lean`.

* Signature/presentation: `S`, `Declared`, `equations`, `M`, `projection`.
* Arbitrary typed family: `associativity_derivable`, `associativity_evaluated`,
  `groupings_distinct`, `quotient_retains_red_count`,
  `red_blue_distinct_in_quotient`.
* Parallel actual arrows: `leftArrow`, `rightArrow`,
  `unequal_parallel_arrows`, `semantic_hom_not_subsingleton`.
* Raw boundary: `rawLeftArrow`, `rawRightArrow`, `raw_fixed_hom_thin`,
  `projection_not_injective`, `right_expansion_has_no_fixed_target_lift`.
* Mixed certificate: `mixed_source_components`, `mixed_target_components`,
  `mixed_groupings_distinct`, `mixed_groupings_equal_in_quotient`,
  `mixedLeftArrow`, `mixedRightArrow`, `mixed_unequal_parallel_arrows`,
  `mixed_semantic_hom_not_subsingleton`,
  `mixed_right_expansion_has_no_fixed_target_lift`, `mixed_witnesses_retained`.
* Nonidentity/nullary composition: `addRed_changes_object`,
  `leftThenRedArrow`, `rightThenRedArrow`, `composed_left_endpoint`,
  `composed_right_endpoint`, `nullaryArrow`, `nullary_frontier_length`,
  `nullary_graft_not_a_unit`.

The A3 quotient implementation uses disclosed standard `Classical.choice` for
representatives, together with Lean's ordinary logical axioms. No custom axiom,
admission, normal-form assumption, or unchecked evaluation oracle is introduced.
The authoritative aggregate build/axiom evidence and independent review, not
this author-stage prose, determine the final verification and acceptance status.
