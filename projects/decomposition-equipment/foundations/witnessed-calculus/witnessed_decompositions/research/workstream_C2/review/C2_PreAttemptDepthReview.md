# C2 non-author pre-attempt depth review

Date: 2026-10-24. Reviewer: `/root/review_relational_model_target`, independent
of the model/proof author and not an implementation contributor. Agent-managed
review; shared-model correlation remains a limitation. This is target review,
not theorem, software, clean-reproduction, or final acceptance certification.

## Decision

**CLEARED FOR PARENT PROOF RELEASE**, for the local C2 positive-M milestone only,
at the following exact input hashes:

- `research/CompletionContract.md`, version 0.1:
  `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
- `research/workstream_C2/C2_Targets.md`:
  `b6711190a46b19205ef25f439105eaf1951137d90f5e55a595ea67daf172e2f4`.

The complete C2 clause, section 3.4, section 13, D2 and E1–E5 were inspected.
The public `CalcData`/`Calc`, `Operation`, occurrence-indexed substitution,
`Signature.Assignment` and free interpretation declarations were also inspected
to test whether the target's requested public-API bridge names actual objects.
The author reported that no proof attempt had begun before this review.

Full C2 remains **OPEN**: its mandated D2/E uses are downstream integration
requirements, not supplied by this local milestone. This review does not
activate D2, E, C3, or any other later work. M allows no obstruction branch.

## Cheapest compliant route and mathematical floor

The cheapest route is the standard predicate-relation semantics on arbitrary
families of finite interface sets, singleton-or-empty containment fibres, and
separately defined equality fibres. Use a complete mathematical proof for all
finite paths and occurrence-indexed substitutions, and independently computed
finite certificates rather than optional full Lean formalization. This is
consistent with C2's P plus L-or-independent-C requirement and section 13.

The elementary binary non-surjectivity example by itself is not enough. The
following additional requirements make this route adequate for the authorized
local model goal rather than a toy shortcut:

1. T1–T2 quantify over every interface family, all binary relations and every
   finite arity, with empty carriers and zero-arity composites included.
   Whole relations are supplied independently; identities, both units,
   substitution and associativity concern the full typed operations.
2. T3 defines actual pullbacks, membership/realizer maps and the correctly
   directed comparison inclusion. Endpoint restrictions and composition of
   restrictions have explicit coherence. Exactness is not presumed.
3. T4 requires a two-sided correspondence with the public A calculus and its
   unique free extension, including actual profile/occurrence transports.
   A separately typed Python table or free syntax relabelled as semantics
   cannot discharge that bridge.
4. F1–F3 fix exhaustive finite domains before computation; F4–F6 supply the
   mixed-interface, repeated-occurrence, syntax-loss, strictness and mutation
   controls. Independent checking computes the certificates rather than
   repeating author assertions.
5. The target claims baseline infrastructure, not a new mathematical invention
   or discharge of the larger equipment integration package.

Excluded routes are tied to the target and contract: singleton-only examples
(C2 floor/F4), defining the whole to be the composite (C2 artifact/T1–T2),
finite tests standing in for the unrestricted theorem (section 3.3/T1–T4),
quotienting syntax by every observed semantic equality (core section 2.3/T4),
conflating exact and containment cells (C2/T2–T3), arbitrary restriction
preserving exactness (T3/F4–F5), replacing the empty composite by the empty
relation (T1/F5), and merging repeated component occurrences (core/T2/F5–F6).

## Boundary defects prevented before proof

- **Nullary exactness:** the empty composite is the diagonal. Its pullback
  along `f` is the kernel relation of `f`; the comparison is diagonal included
  in that kernel relation. Positive-arity internal-surjectivity conditions do
  not imply nullary exactness by vacuity. The target explicitly requires the
  injective nullary case and a noninjective failure certificate.
- **Nullary contraction typing:** restriction/substitution requires maps
  agreeing at every glued interface. A nullary child contracts a loop slot,
  so its two primed endpoint objects and maps must coincide. Equal unprimed
  labels with unrelated endpoint maps are insufficient. T3 now states this.
- **Meaning of strict inclusion:** an inclusion can preserve structure
  strictly without being a proper inclusion in every family. Empty families
  and all-empty carriers can make the two calculi equal. T2 now confines
  properness to the inhabited named certificate.
- **F3 coverage:** every intermediate whole `R_i` containing the block
  composite and every outer whole `W` containing their composite is explicitly
  quantified. Empty segments require the same interface label at both ends,
  not merely equal cardinality.

The reviewed initial draft hash was
`49c42b654bb4b3b473ad54bdc2b101e0a8ffd40f37e754426174ebcabca149fe`.
The latter two clarifications were made before proof release and produce the
cleared target hash above; they restore the intended scope, not weaken it.

## Finite domain checks and later review conditions

Independent combinatorial checks of the frozen cardinality domain yield:

- F1: **113,171** size/function/relation tuples. For `u(n)=1+n+n^2`, this is
  the sum of `u(a)u(b)u(c) 2^(ab+bc)` over `a,b,c` in `{0,1,2}`; it includes
  `0^0=1` and no functions from nonempty sets into the empty set.
- F2: **8,507** relation triples, the sum of `2^(ab+bc+cd)` over four sizes
  in `{0,1,2}`. This is not a claim about the number of individual assertions.
- F3: **9,040** source profiles before segmentations and choices of inner or
  outer wholes. The complete substitution-case count still requires the
  implementation and independent reviewer; no reduced domain is approved.

The F4 sizes `2,3,2` meet the contractual unequal-cardinality requirement;
the three interface labels are distinct despite two equal cardinalities.
This is not a singleton model. It requires a nonempty surviving comparison
side as well as strict loss and a strict nonexact whole.

Later correctness review must inspect the actual all-parameter proofs, not
infer them from test success. In particular it must verify flattening with
empty segments, the distinction between a base-changing map and a fixed-base
`Calc.Hom`, and occurrence-by-occurrence interface compatibility. Reproduction
review must verify the F3 coverage/accounting, the independently written
evaluators, negative controls, and source hashes. Scientific-scope review must
continue to distinguish local baseline verification from full C2 acceptance
and from the mandatory downstream D2/E research contribution.

No implementation files were edited by this reviewer. No unresolved target
defect remains at the cleared hash.
