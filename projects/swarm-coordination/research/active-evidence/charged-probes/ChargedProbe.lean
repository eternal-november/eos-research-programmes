import Mathlib
namespace ChargedProbe

theorem observation_missing_cannot_choose {y : Bool} (action : Bool)
    (left : action = Bool.xor false y) (right : action = Bool.xor true y) :
    False := by
  cases action <;> cases y <;> simp at *

theorem shared_erase_preserves_domination (a b A B : Nat)
    (h₁ : a ≤ A) (h₂ : b ≤ B) (pos : 0 < a) :
    0 < A ∧ a-1 ≤ A-1 ∧ b ≤ B := by omega

theorem isolated_erase_preserves_domination (a b A B : Nat)
    (h₁ : a ≤ A) (h₂ : b ≤ B) (pos : 0 < b) :
    0 < B ∧ a ≤ A ∧ b-1 ≤ B-1 := by omega

theorem fast_mode_reduction (shared idle alt k j : Nat)
    (faster : alt ≤ shared+idle) (count : j < k) :
    (j+1)*alt+(k-(j+1))*(shared+idle) ≤ j*alt+(k-j)*(shared+idle) := by
  have H : k-j=(k-(j+1))+1 := by omega
  rw [H, Nat.add_mul, Nat.add_mul]
  simp only [one_mul]
  omega

end ChargedProbe
#print axioms ChargedProbe.observation_missing_cannot_choose
#print axioms ChargedProbe.shared_erase_preserves_domination
#print axioms ChargedProbe.isolated_erase_preserves_domination
#print axioms ChargedProbe.fast_mode_reduction
