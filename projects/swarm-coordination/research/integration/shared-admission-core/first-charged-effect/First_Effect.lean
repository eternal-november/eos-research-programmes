import Mathlib

namespace FirstEffect

def first {A : Type} (ok : A → Bool) : List A → Option A
  | [] => none
  | x :: xs => if ok x then some x else first ok xs

theorem selects_feasible {A : Type} (ok : A → Bool) (xs : List A) (a : A)
    (h : first ok xs = some a) : a ∈ xs ∧ ok a = true := by
  induction xs with
  | nil => simp [first] at h
  | cons x xs ih =>
    by_cases hx : ok x = true
    · simp [first, hx] at h
      subst a
      exact ⟨by simp, hx⟩
    · have ht : first ok xs = some a := by simpa [first, hx] using h
      rcases ih ht with ⟨mem, yes⟩
      exact ⟨by simp [mem], yes⟩

theorem finds_some {A : Type} (ok : A → Bool) (xs : List A)
    (w : ∃ a ∈ xs, ok a = true) : ∃ a, first ok xs = some a := by
  induction xs with
  | nil => simp at w
  | cons x xs ih =>
    by_cases hx : ok x = true
    · exact ⟨x, by simp [first, hx]⟩
    · have tail : ∃ a ∈ xs, ok a = true := by
        rcases w with ⟨a, ma, ha⟩
        simp only [List.mem_cons] at ma
        cases ma with
        | inl he => subst a; contradiction
        | inr hm => exact ⟨a, hm, ha⟩
      obtain ⟨a, h⟩ := ih tail
      exact ⟨a, by simpa [first, hx] using h⟩

theorem transfer_sound {A : Type} {ok : A → Bool} {xs : List A} {a : A}
    {Settles : A → Prop}
    (source : ∀ x ∈ xs, ok x = true → Settles x)
    (chosen : first ok xs = some a) : Settles a := by
  rcases selects_feasible ok xs a chosen with ⟨mem, yes⟩
  exact source a mem yes

theorem stale_opposite (x : Bool) : ¬ (x = false ∧ x = true) := by
  decide +revert

end FirstEffect
