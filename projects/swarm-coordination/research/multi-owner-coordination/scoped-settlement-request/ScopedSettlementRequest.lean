import Mathlib

namespace ScopedSettlementRequest

theorem exact_one_way_impossible {V : Type} (view : Bool → V) (launch : V → Bool)
    (privacy : view false = view true)
    (safe : launch (view false) = false)
    (live : launch (view true) = true) : False := by
  rw [privacy, live] at safe
  nomatch safe

/-- TV is already bounded on the event of sending the launch command. -/
theorem privacy_tradeoff {epsilon a b : ℝ} (event : b-a ≤ epsilon) :
    1-epsilon ≤ a + (1-b) := by linarith

theorem hard_safety_service {epsilon a b : ℝ} (event : b-a ≤ epsilon) (safe : a=0) :
    b ≤ epsilon := by linarith

theorem no_earlier_effect {r t req rep h issued applied finish : ℝ}
    (role : r + req ≤ issued) (settled : t ≤ issued)
    (reply : issued + rep ≤ applied) (work : applied + h ≤ finish) :
    max t (r + req) + rep + h ≤ finish := by
  have hi := max_le settled role
  linarith

theorem amended_deadline {r t req rep h deadline expiry : ℝ} :
    max t (r+req)+rep+h ≤ min deadline expiry ↔
      max t (r+req)+rep+h ≤ deadline ∧ max t (r+req)+rep+h ≤ expiry :=
  le_min_iff

end ScopedSettlementRequest

#print axioms ScopedSettlementRequest.exact_one_way_impossible
#print axioms ScopedSettlementRequest.privacy_tradeoff
#print axioms ScopedSettlementRequest.hard_safety_service
#print axioms ScopedSettlementRequest.no_earlier_effect
#print axioms ScopedSettlementRequest.amended_deadline
