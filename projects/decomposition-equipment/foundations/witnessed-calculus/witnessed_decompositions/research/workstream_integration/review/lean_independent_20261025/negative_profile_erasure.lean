import IndependentChecks
open TypedNormalizer IndependentIntegrationReview
-- Deliberately invalid: retaining blocks and endpoints does not retain interfaces.
example : E interfaceA interfaceB := by decide
