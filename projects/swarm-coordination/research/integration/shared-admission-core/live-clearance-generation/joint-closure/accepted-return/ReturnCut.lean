import Mathlib
namespace ReturnCut

theorem silence_not_clear (seen : Bool) (safe : ∀ live : Bool, seen = true → live = false) :
    seen = false := by
  cases seen with
  | false => rfl
  | true => have h := safe true rfl; contradiction

theorem receipt_headroom (cap : Nat) (oldFits : 3 ≤ cap) (extra : cap < 6) :
    3 ≤ cap ∧ ¬ 3 + 3 ≤ cap := by omega

theorem no_early_notice_gives_old_room (cap : Nat) :
    (3 + 3 ≤ cap → 3 ≤ cap) := by omega

#print axioms silence_not_clear
#print axioms receipt_headroom
#print axioms no_early_notice_gives_old_room
end ReturnCut
