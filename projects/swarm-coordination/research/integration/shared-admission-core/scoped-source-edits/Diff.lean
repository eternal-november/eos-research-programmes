import Mathlib

namespace Impact

def live {N R D : Type} (radio : R → Prop) (duty : D → Prop)
    (links : N → R → D → Prop) (n : N) (r : R) (d : D) :=
  links n r d ∧ radio r ∧ duty d

/-- Source changes outside old incidence and outside directly changed link
definitions do not change possible history rows for that name. -/
theorem unchanged {N R D : Type}
    (radio radio' : R → Prop) (duty duty' : D → Prop)
    (links links' : N → R → D → Prop) (n : N)
    (sameLink : ∀ r d, links n r d ↔ links' n r d)
    (sameRadio : ∀ r d, links n r d → (radio r ↔ radio' r))
    (sameDuty : ∀ r d, links n r d → (duty d ↔ duty' d)) :
    ∀ r d, live radio duty links n r d ↔ live radio' duty' links' n r d := by
  intro r d
  constructor
  · rintro ⟨l,x,y⟩
    exact ⟨(sameLink r d).mp l,(sameRadio r d l).mp x,(sameDuty r d l).mp y⟩
  · rintro ⟨l,x,y⟩
    have h := (sameLink r d).mpr l
    exact ⟨h,(sameRadio r d h).mpr x,(sameDuty r d h).mpr y⟩

theorem gainedWitness {N R D : Type}
    (radio radio' : R → Prop) (duty duty' : D → Prop)
    (links links' : N → R → D → Prop) (n : N) (r : R) (d : D)
    : (live radio' duty' links' n r d ∧ ¬ live radio duty links n r d) ↔
      (live radio' duty' links' n r d ∧ (¬links n r d ∨ ¬radio r ∨ ¬duty d)) := by
  unfold live
  tauto

/-- A changed link may create a bad alternative without invalidating any
    history that was already present. -/
theorem retainedSuccessInsufficient
    (safe : Bool → Prop) (ss : safe false) (sf : ¬safe true) :
    (∀ x : Bool, x = false → safe x) ∧ ¬(∀ x : Bool, safe x) := by
  constructor
  · intro x h
    simpa [h] using ss
  · intro h
    exact sf (h true)

end Impact

#print axioms Impact.unchanged
#print axioms Impact.gainedWitness
#print axioms Impact.retainedSuccessInsufficient
