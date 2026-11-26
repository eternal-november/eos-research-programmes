import Mathlib

namespace AnonymousVision

def after (before transfer : Bool → Prop) (z : Bool) : Prop :=
  ∃ a b, before a ∧ transfer b ∧ Bool.xor a b = z

theorem lossPersists (before transfer : Bool → Prop)
    (all : ∀ a, before a) (possible : ∃ b, transfer b) :
    ∀ z, after before transfer z := by
  intro z
  obtain ⟨b,hb⟩ := possible
  cases z <;> cases b
  · exact ⟨false,false,all false,hb,rfl⟩
  · exact ⟨true,true,all true,hb,rfl⟩
  · exact ⟨true,false,all true,hb,rfl⟩
  · exact ⟨false,true,all false,hb,rfl⟩

theorem ambiguousTransport (before transfer : Bool → Prop)
    (possible : ∃ a, before a) (all : ∀ b, transfer b) :
    ∀ z, after before transfer z := by
  intro z
  obtain ⟨a,ha⟩ := possible
  cases z <;> cases a
  · exact ⟨false,false,ha,all false,rfl⟩
  · exact ⟨true,true,ha,all true,rfl⟩
  · exact ⟨false,true,ha,all true,rfl⟩
  · exact ⟨true,false,ha,all false,rfl⟩

theorem noNameFromEqualViews {O : Type} (act : O → Bool)
    (x y : O) (same : x = y) :
    ¬(act x = false ∧ act y = true) := by
  subst y
  simp

end AnonymousVision

#print axioms AnonymousVision.lossPersists
#print axioms AnonymousVision.ambiguousTransport
#print axioms AnonymousVision.noNameFromEqualViews
