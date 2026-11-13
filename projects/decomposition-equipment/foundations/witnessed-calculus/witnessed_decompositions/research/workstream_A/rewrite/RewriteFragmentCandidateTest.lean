import RewriteFragmentCandidate
open GraphCoordinates TypedNormalizer RewriteFragmentCandidate

-- Executable regression checks, not replacements for the quantified theorems.
#eval graphCode sixGraph Finset.univ
#eval (normalize (⟨leftMixed, leftMixed_valid⟩ : LocatedTerm Finset.univ 0 2)).val.frontier.blocks.map Finset.card
#eval (normalize (⟨leftMixed, leftMixed_valid⟩ : LocatedTerm Finset.univ 0 2)).val.weight.val
#eval decide (E leftMixed rightBare)
#eval decide (E emptyLeaf (.unit 1 : CutTerm 1 1))
#eval (refinedFirst.frontier.blocks.map Finset.card, refinedSecond.frontier.blocks.map Finset.card)
#eval decide (standardEvaluate sixGraph Finset.univ leftMixed = standardEvaluate sixGraph Finset.univ rightBare)
#eval decide ((evaluate sixGraph Finset.univ rightBare).whole =
  (evaluate missingCrossEdge Finset.univ rightBare).whole)

example : E leftMixed rightBare := mixed_example
example : ¬ E emptyLeaf (.unit 1 : CutTerm 1 1) := empty_leaf_not_nullary
example : ¬ E refinedFirst refinedSecond := different_repeated_occurrence_refinements
#print axioms GraphCoordinates.rankBlock_injective
#print axioms normalizer_sound
#print axioms equiv_iff_standard_cut_eq
#print axioms frontierDispatch_at
