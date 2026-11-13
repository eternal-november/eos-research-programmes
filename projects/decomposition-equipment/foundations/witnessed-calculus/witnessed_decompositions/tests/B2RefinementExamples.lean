import WitnessedDecompositions.RefinementExamples
open WitnessedDecompositions
open WitnessedDecompositions.RefinementExamples

-- The unbounded presentation schema is not limited to the finite checker domain.
example : projection.map (assocLeft 17 23 91 105) =
    projection.map (assocRight 17 23 91 105) := associativity_evaluated _ _ _ _
example : assocLeft 17 23 91 105 ≠ assocRight 17 23 91 105 := groupings_distinct _ _ _ _
example : projection.map (red 17 105) ≠ projection.map (blue 17 105) :=
  red_blue_distinct_in_quotient _ _

-- Genuine interface boundaries, repeated identical positions and nested leaves.
example : component 0 1 ≠ component 1 1 := by
  intro h
  have h' := congrArg Component.source h
  cases h'
example : component 1 1 ≠ component 1 2 := by
  intro h
  have h' := congrArg Component.target h
  cases h'
example : Tree.leaves mixedSource = [component 0 1, x, x, component 1 2] :=
  mixed_source_components
example : (Tree.frontier mixedLeft).length = 5 := mixed_target_five_leaves
example : mixedLeftArrow ≠ mixedRightArrow := mixed_unequal_parallel_arrows
example : Subsingleton (Raw.Arrow root left) := raw_fixed_hom_thin
example : ¬ Subsingleton (SemanticRefinement.Arrow M (projection.map root)
    (projection.map left)) := semantic_hom_not_subsingleton

-- A nonidentity second refinement is actually composed, not erased.
example : projection.map redTarget ≠ projection.map left := addRed_changes_object
example : M.subst (projection.map root) leftThenRedArrow.val =
    projection.map redTarget := composed_left_endpoint
example : M.subst (projection.map root) rightThenRedArrow.val =
    projection.map redTarget := composed_right_endpoint

-- Nullary insertion changes the tuple's segmentation; no unit axiom is assumed.
example : (Tree.frontier nullaryTarget).length = 1 := nullary_frontier_length

example : projection.map nullaryTarget ≠ projection.map (Tree.leaf x) := nullary_graft_not_a_unit
