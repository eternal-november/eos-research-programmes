# C2 failures, revisions and proof limits

Contract and target unchanged. No mathematical target weakening.

## Pre-attempt target review (before proof release)
- First target SHA49c42b654bb4b3b473ad54bdc2b101e0a8ffd40f37e754426174ebcabca149fe
  ambiguously called exact-to-containment inclusion “strict.” Reviewer required
  distinguishing strict structure preservation from properness in an inhabited
  example; universal properness is false for all-empty families.
- Same review required F3 to state explicitly EVERY outer containing W and
  same-label (not merely same-cardinality) empty segments. These were clarified
  before approval; cleared/frozen target b6711190a46b19205ef25f439105eaf1951137d90f5e55a595ea67daf172e2f4.
- Nullary diagonal/kernel-pair and nullary incidence identification requirements
  were explicitly frozen before proof. No counterexample was discovered and
  then hidden by shrinking the approved class.

## Mathematical manuscript review
Initial P SHA0fa36ed07bb21e89aa05eabb6daf6390d966be7d17ec10dff3e3f563016eeb88
was corrected after independent review: unary path composition equals its edge
by the unit law, not definitional reduction; the primitive target was clarified
as public `Operation (S.result g) (S.input g)`, with `S.output g` reserved for
its underlying relation. A concrete nonexact-to-exact endpoint restriction
example was added. Current hash is recorded in the final source snapshot.
No theorem hypothesis or acceptance floor changed.

## Implementation attempts and deliberate failures
Lean elaboration/compilation attempts are retained under `lean/attempt*.log`;
final source and actual axiom audit determine which statements are L. The
formalization's boundary note explains any local elaboration repairs.
Author finite mutations and independent controls deliberately reverse
containment, conflate two different restriction/composition orders, erase
occurrence distinctions, or misuse nullaries. Their rejection is success of
negative testing, not a failed model theorem.

## Explicit nonclaims
P is not L; finite C is not an unrestricted proof. The family is familiar
relational baseline. Full C2 is OPEN pending D2/E use. Sharp general transport
criteria, equipment universal properties, C3 separation program, all other
research workstreams and a program-wide novelty assessment are not activated.
