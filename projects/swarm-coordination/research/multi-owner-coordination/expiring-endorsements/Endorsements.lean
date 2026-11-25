import Mathlib

namespace Endorsements
def retire {C D : Type} (holds : D → C → Bool) (cs : List C) (ds : List D) : List D :=
  ds.filter (fun d => cs.all (holds d))

theorem survival_iff {C D : Type} (holds : D → C → Bool) (cs : List C)
    (ds : List D) (d : D) :
    d ∈ retire holds cs ds ↔ d ∈ ds ∧ ∀ c ∈ cs, holds d c = true := by
  simp [retire, List.all_eq_true]

theorem retire_append {C D : Type} (holds : D → C → Bool)
    (xs ys : List C) (ds : List D) :
    retire holds ys (retire holds xs ds) = retire holds (xs ++ ys) ds := by
  simp [retire, List.filter_filter, List.all_append, Bool.and_comm]

theorem same_down_closure {C D : Type} [Preorder C] (holds : D → C → Bool)
    (law : ∀ (d : D) (a b : C), a ≤ b → holds d b = true → holds d a = true)
    (xs ys : List C)
    (cover : ∀ (c : C), (∃ x ∈ xs, c ≤ x) ↔ (∃ y ∈ ys, c ≤ y))
    (d : D) :
    (∀ c ∈ xs, holds d c = true) ↔ (∀ c ∈ ys, holds d c = true) := by
  constructor
  · intro h c hc
    obtain ⟨x, hx, hcx⟩ := (cover c).mpr ⟨c, hc, le_rfl⟩
    exact law d c x hcx (h x hx)
  · intro h c hc
    obtain ⟨y, hy, hcy⟩ := (cover c).mp ⟨c, hc, le_rfl⟩
    exact law d c y hcy (h y hy)

theorem two_window_mass
    (x00 x10 x01 x11 y00 y10 y01 y11 M : ℕ)
    (hx : x00 + x10 + x01 + x11 = M) (hy : y00 + y10 + y01 + y11 = M)
    (ha : x10 + x11 = y10 + y11) (hb : x01 + x11 = y01 + y11)
    (diff : x11 ≠ y11) : 2 ≤ M := by omega

theorem two_window_sharp :
    ∃ x00 x10 x01 x11 y00 y10 y01 y11 : ℕ,
      x00 + x10 + x01 + x11 = 2 ∧ y00 + y10 + y01 + y11 = 2 ∧
      x10 + x11 = y10 + y11 ∧ x01 + x11 = y01 + y11 ∧ x11 ≠ y11 := by
  exact ⟨1,0,0,1,0,1,1,0, by decide⟩

#print axioms survival_iff
#print axioms retire_append
#print axioms same_down_closure
#print axioms two_window_mass
#print axioms two_window_sharp
end Endorsements
