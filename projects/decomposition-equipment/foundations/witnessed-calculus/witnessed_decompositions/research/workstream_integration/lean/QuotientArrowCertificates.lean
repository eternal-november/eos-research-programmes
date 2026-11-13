import WitnessedDecompositions.PresentedCalculus
import WitnessedDecompositions.SemanticRefinement

/-!
A checked public-API slice of the integration. The arbitrary declared A3
congruence, not a semantic kernel, governs every entry of an actual B2 arrow.
No completeness of a raw categorical completion is assumed or asserted here.
-/
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WitnessedDecompositions.Integration
open Presentation
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u,v,w} V}

noncomputable def rawRepresentative (E : Equations S) {c : Component V}
    (a : (quotient E).Op c) : Tree S c := Quotient.out a

theorem rawRepresentative_projects (E : Equations S) {c : Component V}
    (a : (quotient E).Op c) :
    (projection E).map (rawRepresentative E a) = a := Quotient.out_eq a

/-- The representative has the FULL prescribed path, not just its length. -/
theorem rawRepresentative_profile (E : Equations S) {c : Component V}
    (a : (quotient E).Op c) :
    Tree.frontier (rawRepresentative E a) = (quotient E).profile a :=
  (congruence E).profile_out a

/-- Equality of actual B2 arrows is precisely independent derivability at each
ORIGINAL slot. In particular the endpoint equation is never used to equate two
different tuples. Empty source profiles and repeated component types are allowed. -/
theorem arrow_eq_iff_entry_derives (E : Equations S) {c : Component V}
    {a b : (quotient E).Op c}
    (f g : SemanticRefinement.Arrow (quotient E) a b) :
    f = g ↔ ∀ i, Derives S E (rawRepresentative E (f.val i))
      (rawRepresentative E (g.val i)) := by
  constructor
  · rintro rfl i
    exact Derives.refl _
  · intro h
    apply Subtype.ext
    funext i
    have hi := (quotient_eq_iff E _ _).mpr (h i)
    simpa only [rawRepresentative_projects] using hi

/-- An independently proved operation normalizer lifts to an EXACT arrow-code
criterion, not merely a sufficient categorical-faithfulness assumption.
`complete` is the local operation equality theorem; no arrow conclusion is a
hypothesis. This generic bridge is instantiated by the P-level A4/API adapter. -/
theorem arrow_eq_iff_entry_codes (E : Equations S)
    (Code : Component V → Type z)
    (code : ∀ {c}, Tree S c → Code c)
    (complete : ∀ {c} (s t : Tree S c), code s = code t ↔ Derives S E s t)
    {c : Component V} {a b : (quotient E).Op c}
    (f g : SemanticRefinement.Arrow (quotient E) a b) :
    f = g ↔ ∀ i, code (rawRepresentative E (f.val i)) =
      code (rawRepresentative E (g.val i)) := by
  rw [arrow_eq_iff_entry_derives]
  constructor
  · intro h i
    exact (complete _ _).mpr (h i)
  · intro h i
    exact (complete _ _).mp (h i)

/-- Derived per-entry equality also preserves each entry's own full profile;
this is stronger than equality of their concatenated target profiles. -/
theorem entry_profiles_of_derives (E : Equations S) {c : Component V}
    {a b : (quotient E).Op c}
    (f g : SemanticRefinement.Arrow (quotient E) a b)
    (h : ∀ i, Derives S E (rawRepresentative E (f.val i))
      (rawRepresentative E (g.val i))) :
    ∀ i, (quotient E).profile (f.val i) = (quotient E).profile (g.val i) := by
  have he := (arrow_eq_iff_entry_derives E f g).mpr h
  cases he
  intro i
  rfl

/-- Equality certified entrywise survives actual B2 composition on both sides,
whose implementation uses typed descendant occurrences, not leaf labels. -/
theorem compose_entry_certificates (E : Equations S) {c : Component V}
    {a b d : (quotient E).Op c}
    (f f' : SemanticRefinement.Arrow (quotient E) a b)
    (g g' : SemanticRefinement.Arrow (quotient E) b d)
    (hf : ∀ i, Derives S E (rawRepresentative E (f.val i))
      (rawRepresentative E (f'.val i)))
    (hg : ∀ i, Derives S E (rawRepresentative E (g.val i))
      (rawRepresentative E (g'.val i))) :
    SemanticRefinement.comp f g = SemanticRefinement.comp f' g' := by
  exact congrArg₂ SemanticRefinement.comp
    ((arrow_eq_iff_entry_derives E f f').mpr hf)
    ((arrow_eq_iff_entry_derives E g g').mpr hg)

/-- The bridge compares the actual strict projection on actual semantic arrows. -/
theorem projection_arrow_comp (E : Equations S) {c : Component V}
    {a b d : Tree S c}
    (f : SemanticRefinement.Arrow (Tree.freeCalc S) a b)
    (g : SemanticRefinement.Arrow (Tree.freeCalc S) b d) :
    SemanticRefinement.mapArrow (projection E) (SemanticRefinement.comp f g) =
      SemanticRefinement.comp (SemanticRefinement.mapArrow (projection E) f)
        (SemanticRefinement.mapArrow (projection E) g) :=
  SemanticRefinement.mapArrow_comp (projection E) f g

theorem projection_arrow_identity (E : Equations S) {c : Component V}
    (a : Tree S c) :
    SemanticRefinement.mapArrow (projection E) (SemanticRefinement.id a) =
      SemanticRefinement.id ((projection E).map a) :=
  SemanticRefinement.mapArrow_id (projection E) a

end WitnessedDecompositions.Integration
