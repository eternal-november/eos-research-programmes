import Lean

namespace ObservationFiber

universe u v w
variable {H : Type u} {W : Type v} {O : Type w}
variable (law : H → W) (obs : H → O) (paid : H → Bool)

def precise (admit : W → Prop) (r : O) (z : Bool) : Prop :=
  ∃ h, admit (law h) ∧ obs h = r ∧ paid h = z

def expanded (admit : W → Prop) (r : O) (z : Bool) : Prop :=
  ∃ h k, admit (law h) ∧ obs h = r ∧ law k = law h ∧ paid k = z

theorem no_lost_outcome (A : W → Prop) (r : O) (z : Bool) :
    precise law obs paid A r z → expanded law obs paid A r z := by
  rintro ⟨h, ha, hr, hz⟩
  exact ⟨h,h,ha,hr,rfl,hz⟩

/-- Equality across arbitrary law restrictions iff every feasible observation
has all outcome bits that its installation can exhibit. -/
theorem exact_iff :
    (∀ (A : W → Prop) (r : O) (z : Bool),
      expanded law obs paid A r z ↔ precise law obs paid A r z) ↔
    (∀ h k, law k = law h → ∃ t, law t = law h ∧ obs t = obs h ∧ paid t = paid k) := by
  constructor
  · intro eq h k same
    let A : W → Prop := fun w => w = law h
    have ex : expanded law obs paid A (obs h) (paid k) := ⟨h,k,rfl,rfl,same,rfl⟩
    exact (eq A (obs h) (paid k)).mp ex
  · intro sat A r z
    constructor
    · rintro ⟨h,k,ha,hr,hk,hz⟩
      obtain ⟨t,ht,ho,hp⟩ := sat h k hk
      exact ⟨t,ht ▸ ha,ho.trans hr,hp.trans hz⟩
    · exact no_lost_outcome law obs paid A r z

theorem nonempty_same (A : W → Prop) (r : O) :
    (∃ z, expanded law obs paid A r z) ↔ (∃ z, precise law obs paid A r z) := by
  constructor
  · rintro ⟨_,h,_,ha,hr,_,_⟩
    exact ⟨paid h,h,ha,hr,rfl⟩
  · rintro ⟨z,h⟩
    exact ⟨z,no_lost_outcome law obs paid A r z h⟩

#print axioms no_lost_outcome
#print axioms exact_iff
#print axioms nonempty_same

end ObservationFiber
