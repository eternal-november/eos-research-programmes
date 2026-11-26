import Lean
namespace HostedPrefix

def hostedEnd (clear atHold : Nat) := if atHold<clear then clear+1 else clear

theorem tight_fails (clear atHold deadline : Nat) (h : clear=deadline)
    (earlier : atHold<clear) : ¬ hostedEnd clear atHold ≤ deadline := by
  subst deadline
  simp [hostedEnd,earlier]

theorem one_margin (clear atHold deadline : Nat) (earlier : atHold<clear) :
    hostedEnd clear atHold ≤ deadline ↔ clear < deadline := by
  simp [hostedEnd,earlier]
  omega

theorem output_cannot_refund (clear atHold deadline : Nat)
    (h : clear=deadline) (earlier : atHold<clear)
    (choose : Bool → Bool) :
    ¬∃ returned, choose returned = false ∧ hostedEnd clear atHold ≤ deadline := by
  rintro ⟨_,_,stays⟩
  exact tight_fails clear atHold deadline h earlier stays

theorem independent_spare (clear deadline : Nat) (res : Nat)
    (clear_ok : clear≤deadline) :
    (clear≤deadline ∧ 1≤res) ↔ res>0 := by
  omega

#print axioms tight_fails
#print axioms one_margin
#print axioms output_cannot_refund
#print axioms independent_spare
end HostedPrefix
