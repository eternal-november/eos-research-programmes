import Mathlib
namespace ScopedDoor
def nativeRelease (openStamp closeStamp : Nat) : Prop := openStamp ≤ closeStamp

theorem equal_time_accepted (t : Nat) : nativeRelease t t := Nat.le_refl t

theorem strictly_old_rejected {old current : Nat} (h : old < current) :
    ¬ nativeRelease current old := by
  unfold nativeRelease
  omega

theorem same_message_no_local_distinction {Msg : Type} (choose : Msg → Bool)
    {old current : Msg} (same : old = current) :
    ¬ (choose old = false ∧ choose current = true) := by
  rw [same]
  rintro ⟨off, on⟩
  simp [off] at on

def scopedRelease (live supplied openStamp closeStamp : Nat) : Prop :=
  live = supplied ∧ nativeRelease openStamp closeStamp

theorem scope_can_distinguish (t : Nat) :
    ¬ scopedRelease 7 6 t t ∧ scopedRelease 7 7 t t := by
  unfold scopedRelease nativeRelease
  omega
end ScopedDoor
