import IndependentChecks
open TypedNormalizer IndependentIntegrationReview
-- Deliberately invalid: cancellation is not available in the finite idempotent monoid.
example : E e1 (.deco Idem.absorb e1) := by decide
