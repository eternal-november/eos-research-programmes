import Mathlib

namespace RetirementPrerequisite

def Up {K : Type} (r : K → K → Prop) (A : Set K) : Set K :=
  { x | ∃ a ∈ A, r a x }

theorem collapse_of_weaker_prerequisites {K : Type} (r s : K → K → Prop)
    (refl : ∀ x, r x x) (incl : ∀ ⦃x y⦄, r x y → s x y)
    (trans : ∀ ⦃x y z⦄, s x y → s y z → s x z) (A : Set K) :
    Up s (Up r A) = Up s A := by
  ext x
  constructor
  · rintro ⟨b,⟨a,ha,hab⟩,hbx⟩
    exact ⟨a,ha,trans (incl hab) hbx⟩
  · rintro ⟨a,ha,hax⟩
    exact ⟨a,⟨a,ha,refl a⟩,hax⟩

theorem surviving_scope_test {K : Type} (r : K → K → Prop)
    (refl : ∀ x, r x x) (A U : Set K)
    (up : ∀ ⦃x y⦄, x ∈ U → r x y → y ∈ U) :
    Up r A ⊆ U ↔ A ⊆ U := by
  constructor
  · intro h x hx
    exact h ⟨x,hx,refl x⟩
  · intro h x hx
    rcases hx with ⟨a,ha,hax⟩
    exact up (h ha) hax

#print axioms collapse_of_weaker_prerequisites
#print axioms surviving_scope_test

end RetirementPrerequisite
