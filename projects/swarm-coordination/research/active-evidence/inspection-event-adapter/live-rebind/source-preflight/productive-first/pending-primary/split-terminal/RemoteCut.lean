import Lean
namespace RemoteCut
def paid (revoke primary returned fallback : Bool) : Bool :=
  if revoke then returned && fallback else primary

theorem lack_of_return_scope :
    ¬∃ decision : Bool,
      paid decision true false true = true ∧
      paid decision false true true = true := by
  rintro ⟨decision,h⟩
  cases decision <;> simp [paid] at h

theorem exactly_one_role (revoked primary fallback : Bool)
    (p : primary = true → revoked = false)
    (f : fallback = true → revoked = true) :
    ¬ (primary = true ∧ fallback = true) := by
  rintro ⟨h₁,h₂⟩
  have h := (p h₁).symm.trans (f h₂)
  contradiction

theorem shared_reply_needs_headroom {cap old reply alternate : Nat}
    (r : old+reply ≤ cap) (notBoth : cap < old+reply+alternate) :
    old+reply ≤ cap ∧ ¬ (old+reply+alternate ≤ cap) := by omega

#print axioms lack_of_return_scope
#print axioms exactly_one_role
#print axioms shared_reply_needs_headroom
end RemoteCut
