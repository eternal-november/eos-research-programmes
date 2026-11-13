import IndependentChecks
open TypedNormalizer RewriteFragmentCandidate IntegrationGraphForest
-- Deliberately invalid: source occurrence zero is 0→1, not 1→1.
example : CutTerm 0 1 := cancellingForest ⟨1, by decide⟩
