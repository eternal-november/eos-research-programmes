# Joint decoder formalization coverage

2 November 2026

## What is proved

`JointQuotientDecoder.lean` formalizes the exact set-valued whole-record image equation. For concrete relation P, source encoder q, record encoder r and abstract relation A, an exact decoder exists precisely when sources with the same code have the same sets of encoded **whole** records. Exactness is equivalent to forward soundness plus lifting every abstract record at **each specified concrete source**. Uniqueness is proved on a surjective abstract source carrier; arbitrary unused source codes are not silently constrained.

The record type is unrestricted: a dependent occurrence-indexed tuple, a record containing a witness and factors, or a retained pair of intermediate and final records can all be used. `exact_compose_records` proves the two-step relation law without discarding the intermediate witness.

Deterministic operations have a separate gate. `descends_iff_kernelCompatible` and `graft_descends_iff` prove precisely when unary transport and dependent occurrence-indexed grafting descend. Their commuting squares compose. These theorems do not infer graft congruence from cut stability.

A fixed typed signature declares atoms, deterministic steps, cut shapes, each shape's finite arity, and each child's type. The generated `Test` language has atoms, negation, conjunction, steps and existential joint cuts. `generated_tests_preserved` is an induction for every such typed test. A cut chooses one complete record before testing all children, retaining the same correlations. A zero-child cut retains its feasibility predicate; its empty conjunction does not assert that an empty record exists.

`JointArrayDecoderBridge.lean` instantiates the generic exact-decoder premise using the independently proved joint-array lifting theorem. With the fixed covered edge-path incidence, injective monoid map and factor-closed image, the concrete array relation is exactly decoded by entrywise transport. All intermediate word products use the same array. Thus the generated-decoder premise has an actual substantive instance, not merely an assumed name.

## Checked boundary examples

- Equal first and second Boolean marginals do not determine a binary joint relation (diagonal versus antidiagonal).
- Merging sources with different empty-record feasibility admits no exact source-fixed decoder.
- A trivial cut relation can be exact under projection to one Boolean while coordinate-swap transport fails to descend.

## Relationship to source mathematics

These modules mechanize the generic exact-image equation and syntax-induction mechanism used in I2/I5, with the later full-unital correction retained. They are standard relational/behavioral quotient infrastructure, not claims of a new minimization theory. The array bridge uses the repaired I1 lifting theorem at its explicit coefficient-incidence scope. The modules do not prove all-profile graph admissibility, categorical equipment completion, maximality/minimality of every observation repair, witness multiplicity preservation, or a physical realization theorem. The rank-sensitive proper quotient is separately instantiated by the compression module.

The formal test language covers finite laminar generated tests with prescribed typed steps and cuts. It does not add equality tests between hidden factors, arbitrary crossing/shared-variable constraints across subtrees, probabilities, or witness counts. Quantifying over all predicates on an encoded complete record is a generic preservation lemma, not an authorization to expose hidden data as a programme observation.

## Build and assurance

Use the shared project's pinned Lean 4.35.0/mathlib environment. Build the kernel first, then:

    lake env lean -o .lake/build/lib/lean/JointQuotientDecoder.olean JointQuotientDecoder.lean
    lake env lean -o .lake/build/lib/lean/JointArrayDecoderBridge.olean JointArrayDecoderBridge.lean
    lake env lean JointQuotientDecoderAudit.lean
    lake env lean JointArrayDecoderBridgeAudit.lean

The source sets `autoImplicit false`. There are no `sorry`, `admit`, or new axioms. The generated-test preservation, exact soundness/lifting equivalence, record composition, empty-feasibility obstruction and swap obstruction use no axioms. Chosen descents/array inverse constructions may use the usual Lean classical-choice, propositional-extensionality and quotient-soundness axioms; the audit records the exact dependency list. Compilation is kernel checking of these stated declarations, not certification of an unstated broader programme.
