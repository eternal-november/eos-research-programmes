import WitnessedDecompositions.RefinementComparison
import WitnessedDecompositions.RefinementFunctoriality
import WitnessedDecompositions.RefinementExamples
open WitnessedDecompositions
open CategoryTheory
open WitnessedDecompositions.RefinementExamples
open WitnessedDecompositions.RefinementComparison
set_option backward.isDefEq.respectTransparency false

-- Direct hom-map failure for the actual implemented raw functor, not merely
-- failure of one selected forest representative or collapse of object names.
theorem reviewer_actual_raw_map_not_full :
    ¬ Function.Surjective (fun f : Raw.Arrow root left =>
      (rawFunctor projection x).map f) := by
  intro h
  obtain ⟨f,hf⟩ := h rightArrow
  apply right_expansion_has_no_fixed_target_lift
  refine ⟨(Tree.profileSubstitutionEquiv root).symm f.val, ?_, ?_⟩
  · exact (rawToFreeArrow f).property
  · exact congrArg Subtype.val hf

theorem reviewer_actual_mixed_raw_map_not_full :
    ¬ Function.Surjective (fun f : Raw.Arrow mixedSource mixedLeft =>
      (rawFunctor projection (component 0 2)).map f) := by
  intro h
  obtain ⟨f,hf⟩ := h mixedRightArrow
  apply mixed_right_expansion_has_no_fixed_target_lift
  refine ⟨(Tree.profileSubstitutionEquiv mixedSource).symm f.val, ?_, ?_⟩
  · exact (rawToFreeArrow f).property
  · exact congrArg Subtype.val hf

-- Explicit inverse functors, arbitrary signature, interfaces and nullary choices.
example {V : Type} [Quiver V] (S : Signature V) (c : Component V) :
    rawToFree S c ⋙ freeToRaw S c = CategoryTheory.Functor.id (Tree S c) :=
  rawToFree_freeToRaw_functor S c

#print axioms reviewer_actual_raw_map_not_full
#print axioms reviewer_actual_mixed_raw_map_not_full
