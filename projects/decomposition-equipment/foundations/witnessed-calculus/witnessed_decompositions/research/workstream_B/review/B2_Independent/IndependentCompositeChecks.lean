import WitnessedDecompositions.RefinementExamples
open WitnessedDecompositions
open WitnessedDecompositions.RefinementExamples
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

-- A reviewer check of retained tuple segmentation after genuine nonidentity
-- composition, not merely the composite's already-certified endpoint.
example : (M.profile (leftThenRedArrow.val (Sum.inl (Sum.inr ())))).length = 2 := by
  change (M.profile (M.subst _ _)).length = 2
  rw [M.profile_subst]
  rfl

example : (M.profile (rightThenRedArrow.val (Sum.inl (Sum.inr ())))).length = 1 := by
  change (M.profile (M.subst _ _)).length = 1
  rw [M.profile_subst]
  rfl

 theorem reviewer_composed_arrows_unequal : leftThenRedArrow ≠ rightThenRedArrow := by
  intro h
  have hp := congrArg (fun f : SemanticRefinement.Arrow M (projection.map root)
    (projection.map redTarget) => (M.profile (f.val (Sum.inl (Sum.inr ())))).length) h
  have hL : (M.profile (leftThenRedArrow.val (Sum.inl (Sum.inr ())))).length = 2 := by
    change (M.profile (M.subst _ _)).length = 2
    rw [M.profile_subst]
    rfl
  have hR : (M.profile (rightThenRedArrow.val (Sum.inl (Sum.inr ())))).length = 1 := by
    change (M.profile (M.subst _ _)).length = 1
    rw [M.profile_subst]
    rfl
  rw [hL,hR] at hp
  cases hp

example : SemanticRefinement.comp (SemanticRefinement.id _) leftArrow = leftArrow :=
  SemanticRefinement.id_comp _
example : SemanticRefinement.comp leftArrow (SemanticRefinement.id _) = leftArrow :=
  SemanticRefinement.comp_id _
example : SemanticRefinement.comp (SemanticRefinement.comp leftArrow addRedArrow)
    (SemanticRefinement.id _) =
    SemanticRefinement.comp leftArrow
      (SemanticRefinement.comp addRedArrow (SemanticRefinement.id _)) :=
  SemanticRefinement.assoc _ _ _
example : SemanticRefinement.comp (SemanticRefinement.id _) nullaryArrow = nullaryArrow :=
  SemanticRefinement.id_comp _
example : SemanticRefinement.comp nullaryArrow (SemanticRefinement.id _) = nullaryArrow :=
  SemanticRefinement.comp_id _
#print axioms reviewer_composed_arrows_unequal
