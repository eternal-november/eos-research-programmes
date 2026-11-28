import Mathlib
namespace JointCut

variable {H A : Type} [Fintype A] [DecidableEq H]

-- H is one nonempty reached observation cell, not the whole world set.
-- A is the finite positive-service action menu, not the refusal action.
theorem finite_cell_obstruction (good : H → A → Prop)
    (bad : ¬ ∃ a, ∀ h, good h a) :
    ∃ s : Finset H, s.card ≤ Fintype.card A ∧
      ∀ a, ∃ h ∈ s, ¬ good h a := by
  classical
  have witnesses : ∀ a, ∃ h, ¬ good h a := by
    intro a
    by_contra hh
    push Not at hh
    exact bad ⟨a, hh⟩
  choose w hw using witnesses
  refine ⟨Finset.univ.image w, (Finset.card_image_le), ?_⟩
  intro a
  exact ⟨w a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, hw a⟩

-- A different single blocked action per history makes the general bound sharp.
theorem diagonal_obstruction_iff (s : Finset A) :
    (∀ a : A, ∃ h ∈ s, ¬ (h ≠ a)) ↔ s = Finset.univ := by
  classical
  constructor
  · intro hs
    apply Finset.eq_univ_of_forall
    intro a
    obtain ⟨h, hmem, he⟩ := hs a
    simpa [not_ne_iff.mp he] using hmem
  · rintro rfl a
    exact ⟨a, Finset.mem_univ a, not_not_intro rfl⟩

def signal (h : Fin 3) : Bool := h == 0
def decideAct (b : Bool) : Fin 3 := if b then 1 else 0

theorem fresh_membership_suffices (h : Fin 3) : decideAct (signal h) ≠ h := by
  fin_cases h <;> decide

theorem every_pair_works (h k : Fin 3) : ∃ a : Fin 3, a ≠ h ∧ a ≠ k := by
  fin_cases h <;> fin_cases k <;> decide

theorem all_three_fail : ¬ ∃ a : Fin 3, ∀ h : Fin 3, a ≠ h := by
  rintro ⟨a, ha⟩
  exact ha a rfl

def summary (good : H → A → Prop) (cell : Set H) : Set A :=
  {a | ∀ h ∈ cell, good h a}

omit [Fintype A] [DecidableEq H] in
theorem cell_merge (good : H → A → Prop) (left right : Set H) :
    summary good (left ∪ right) = summary good left ∩ summary good right := by
  ext a
  constructor
  · intro ok
    exact ⟨fun h hh => ok h (Or.inl hh), fun h hh => ok h (Or.inr hh)⟩
  · rintro ⟨hl, hr⟩ h (hh | hh)
    exacts [hl h hh, hr h hh]

-- Joint late-cell summary is exact (and distinction-minimal) for an
-- interface whose downstream observer can impose any further action menu.
omit [Fintype A] in
theorem restriction_tests_reflect (p q : Set A) :
    (∀ restrict : Set A, (p ∩ restrict).Nonempty ↔ (q ∩ restrict).Nonempty)
     ↔ p = q := by
  constructor
  · intro tests
    ext a
    constructor
    · intro h
      obtain ⟨b, hbp, hb⟩ := (tests {a}).1 ⟨a, h, Set.mem_singleton a⟩
      simpa [Set.mem_singleton_iff.mp hb] using hbp
    · intro h
      obtain ⟨b, hbp, hb⟩ := (tests {a}).2 ⟨a, h, Set.mem_singleton a⟩
      simpa [Set.mem_singleton_iff.mp hb] using hbp
  · rintro rfl
    simp
end JointCut
