import Mathlib

namespace SwarmScopedAdvice

def Profile {α : Type} (scope history : Set α) : Set α :=
  history ∩ scope

theorem profile_eq_iff_agreement {α : Type} (scope s t : Set α) :
    Profile scope s = Profile scope t ↔
      ∀ q ∈ scope, q ∈ s ↔ q ∈ t := by
  constructor
  · intro h q hq
    have e : q ∈ Profile scope s ↔ q ∈ Profile scope t := by rw [h]
    simpa [Profile, hq] using e
  · intro h
    ext q
    by_cases hq : q ∈ scope
    · simpa [Profile, hq] using h q hq
    · simp [Profile, hq]

theorem exact_report_refines_profile {α Code : Type} (scope s t : Set α)
    (encode : Set α → Code) (ask : Code → α → Prop)
    (hask : ∀ h q, q ∈ scope → (ask (encode h) q ↔ q ∈ h))
    (h : encode s = encode t) :
    Profile scope s = Profile scope t := by
  apply (profile_eq_iff_agreement scope s t).mpr
  intro q hq
  rw [← hask s q hq, ← hask t q hq, h]

theorem undisclosed_swap_preserves_profile {α : Type} (scope s : Set α)
    (a b : α) (ha : a ∉ scope) (hb : b ∉ scope) :
    Profile scope s = Profile scope ((s \ {a}) ∪ {b}) := by
  apply (profile_eq_iff_agreement _ _ _).mpr
  intro q hq
  have hqa : q ≠ a := by rintro rfl; exact ha hq
  have hqb : q ≠ b := by rintro rfl; exact hb hq
  simp [hqa, hqb]

theorem extending_scope_can_require_new_evidence
    {α Code : Type} (oldScope newScope s t : Set α) (a : α)
    (hold : Profile oldScope s = Profile oldScope t)
    (ha : a ∈ newScope) (hs : a ∈ s) (ht : a ∉ t)
    (encode : Set α → Code) (ask : Code → α → Prop)
    (privateReport : ∀ u v, Profile oldScope u = Profile oldScope v → encode u = encode v) :
    ¬ (∀ h q, q ∈ newScope → (ask (encode h) q ↔ q ∈ h)) := by
  intro he
  have hn := exact_report_refines_profile newScope s t encode ask he
    (privateReport s t hold)
  exact ht ((profile_eq_iff_agreement newScope s t).mp hn a ha |>.mp hs)

#print axioms profile_eq_iff_agreement
#print axioms exact_report_refines_profile
#print axioms undisclosed_swap_preserves_profile
#print axioms extending_scope_can_require_new_evidence
end SwarmScopedAdvice
