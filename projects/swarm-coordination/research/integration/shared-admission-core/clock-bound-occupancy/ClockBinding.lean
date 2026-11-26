import Lean
namespace ClockBinding

def Hits (a b delta l r s : Int) : Prop :=
  ∃ t : Int, a+delta ≤ t ∧ t < b+delta ∧ s+l ≤ t ∧ t < s+r

theorem hits_iff (a b delta l r s : Int) (hb : a < b) (hr : l < r) :
    Hits a b delta l r s ↔ a+delta-r < s ∧ s < b+delta-l := by
  unfold Hits
  constructor
  · rintro ⟨t,h₁,h₂,h₃,h₄⟩
    omega
  · intro h
    by_cases k : s+l ≤ a+delta
    · refine ⟨a+delta, by omega, ?_, k, ?_⟩ <;> omega
    · refine ⟨s+l, ?_, ?_, by omega, ?_⟩ <;> omega

theorem horizon_iff (delta size l r s : Int) (hr : l < r) :
    (∀ t : Int, s+l ≤ t → t < s+r → delta ≤ t ∧ t < delta+size) ↔
      delta-l ≤ s ∧ s ≤ delta+size-r := by
  constructor
  · intro h
    have a := h (s+l) (by omega) (by omega)
    have b := h (s+r-1) (by omega) (by omega)
    omega
  · intro h t hlo hhi
    omega

theorem actual_gap_certified :
    ¬ Hits 7 17 3 0 2 8 ∧ ¬ Hits 30 31 3 0 2 8 ∧
    ¬ Hits 0 6 0 0 2 8 ∧ ¬ Hits 19 32 0 0 2 8 := by
  unfold Hits
  omega

theorem flipped_binding_counterhistory :
    Hits 7 17 0 0 2 8 ∧ Hits 0 6 3 0 2 8 := by
  constructor
  · exact ⟨8, by decide, by decide, by decide, by decide⟩
  · exact ⟨8, by decide, by decide, by decide, by decide⟩

#print axioms hits_iff
#print axioms horizon_iff
#print axioms actual_gap_certified
#print axioms flipped_binding_counterhistory
end ClockBinding
