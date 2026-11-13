import WitnessedDecompositions.RefinementComparison
import WitnessedDecompositions.RefinementExamples

open WitnessedDecompositions
open WitnessedDecompositions.Tree
open WitnessedDecompositions.RefinementComparison
open WitnessedDecompositions.RefinementExamples

namespace WitnessedDecompositions.RefinementComparisonChecks

/-- Direct failure of surjectivity of the actual raw evaluation functor's
fixed root→left hom map, rather than only failure of a guessed representative. -/
theorem right_arrow_not_in_raw_functor_image :
    ¬ ∃ f : Raw.Arrow root left, (rawFunctor projection x).map f = rightArrow := by
  rintro ⟨f,h⟩
  apply right_expansion_has_no_fixed_target_lift
  refine ⟨(Tree.profileSubstitutionEquiv root).symm f.val, ?_, ?_⟩
  · exact (rawToFreeArrow f).property
  · have hh := congrArg Subtype.val h
    exact hh

/-- The same actual-functor nonlifting statement in the mixed-interface context. -/
theorem mixed_right_arrow_not_in_raw_functor_image :
    ¬ ∃ f : Raw.Arrow mixedSource mixedLeft,
      (rawFunctor projection (component 0 2)).map f = mixedRightArrow := by
  rintro ⟨f,h⟩
  apply mixed_right_expansion_has_no_fixed_target_lift
  refine ⟨(Tree.profileSubstitutionEquiv mixedSource).symm f.val, ?_, ?_⟩
  · exact (rawToFreeArrow f).property
  · have hh := congrArg Subtype.val h
    exact hh

#print axioms right_arrow_not_in_raw_functor_image
#print axioms mixed_right_arrow_not_in_raw_functor_image

end WitnessedDecompositions.RefinementComparisonChecks
