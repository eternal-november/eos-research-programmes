import IndependentChecks
open TypedNormalizer IntegrationGraphForest
-- Deliberately invalid: deleting a nullary must not erase its nonidentity value.
example : E labelledNullary (.unit 1) := by decide
