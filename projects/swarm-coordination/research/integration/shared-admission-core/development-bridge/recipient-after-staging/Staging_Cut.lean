import Mathlib
namespace StagingCut

variable {W O D : Type} (v : W → O) (ok : W → D → Prop) (staged : D → Prop)

theorem carrierLaw [Nonempty W] :
    (∃ select : O → D, ∀ w, staged (select (v w)) ∧ ok w (select (v w))) ↔
    (∀ o, (∃ w, v w = o) → ∃ d, staged d ∧ ∀ w, v w = o → ok w d) := by
  classical
  constructor
  · rintro ⟨s,h⟩ o ⟨w0,h0⟩
    refine ⟨s o, ?_, ?_⟩
    · simpa [h0] using (h w0).1
    · intro w hw
      simpa [hw] using (h w).2
  · intro h
    let init : W := Classical.choice inferInstance
    let default := (h (v init) ⟨init,rfl⟩).choose
    let select : O → D := fun o => if h0 : ∃ w, v w = o then (h o h0).choose else default
    refine ⟨select, ?_⟩
    intro w
    have hw : ∃ w', v w' = v w := ⟨w,rfl⟩
    simpa [select,hw] using And.intro (h (v w) hw).choose_spec.1
      ((h (v w) hw).choose_spec.2 w rfl)

theorem merged_empty_impossible (a b : W) (same : v a = v b)
    (incompatible : ∀ d, ¬ (ok a d ∧ ok b d)) :
    ¬ (∃ select : O → D, ∀ w, ok w (select (v w))) := by
  rintro ⟨s,h⟩
  exact incompatible (s (v a)) ⟨h a, by simpa [same] using h b⟩

theorem late_selector_cut (frame query extra cap : Nat)
    (localFits : frame + query ≤ cap)
    (sharedMisses : cap < frame + query + extra) :
    frame + query ≤ cap ∧ ¬ frame + query + extra ≤ cap :=
  ⟨localFits,not_le.mpr sharedMisses⟩
end StagingCut
