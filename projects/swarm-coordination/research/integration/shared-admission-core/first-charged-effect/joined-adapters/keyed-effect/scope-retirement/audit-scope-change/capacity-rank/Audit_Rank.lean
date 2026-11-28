import Mathlib
namespace AuditRank

theorem four_of_six_not_octet (encode : Fin 360 → Fin 256) :
    ¬ Function.Injective encode := by
  intro h
  have le := Fintype.card_le_of_injective encode h
  simp at le

def three_of_six_octet (x : Fin 120) : Fin 256 :=
  ⟨x.val, Nat.lt_trans x.isLt (by decide)⟩

theorem three_of_six_fits : Function.Injective three_of_six_octet := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 256 => x.val) h

theorem class_counts :
    6 * 5 * 4 = 120 ∧ 6 * 5 * 4 * 3 = 360 := by decide

end AuditRank
