import IndependentChecks
open TypedNormalizer GraphCoordinates RewriteFragmentCandidate IntegrationGraphForest
-- Deliberately invalid: equality of grafted composites does not identify tuples.
example : forestNormal rightBare cancellingForest = forestNormal rightBare (identityForest rightBare) := by
  exact equal_grafts_unequal_forest_codes.1
