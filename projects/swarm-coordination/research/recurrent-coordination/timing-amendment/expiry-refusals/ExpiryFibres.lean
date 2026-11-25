import Mathlib

namespace ExpiryFibres

variable {A I : Type}

def Pass (e : I → Nat) : Option (I × Nat) → Prop
  | none => True
  | some (i, t) => e i ≤ t

/-- Words are reversed; the head is the next event added to the prefix. -/
def Good (core : List A → A → Prop) (tag : List A → A → Option (I × Nat))
    (e : I → Nat) : List A → Prop
  | [] => True
  | a :: p => Good core tag e p ∧ core p a ∧ Pass e (tag p a)

theorem same_iff_frontier (core : List A → A → Prop) (tag : List A → A → Option (I × Nat))
    (e f : I → Nat) :
    (∀ w, Good core tag e w ↔ Good core tag f w) ↔
    (∀ p a, Good core tag e p → core p a → (Pass e (tag p a) ↔ Pass f (tag p a))) := by
  constructor
  · intro same p a hp hcore
    have hpf := (same p).mp hp
    constructor
    · intro h
      exact ((same (a :: p)).mp ⟨hp, hcore, h⟩).2.2
    · intro h
      exact ((same (a :: p)).mpr ⟨hpf, hcore, h⟩).2.2
  · intro frontier w
    induction w with
    | nil => rfl
    | cons a p ih =>
      constructor
      · intro ⟨hp, hc, ht⟩
        exact ⟨ih.mp hp, hc, (frontier p a hp hc).mp ht⟩
      · intro ⟨hp, hc, ht⟩
        exact ⟨ih.mpr hp, hc, (frontier p a (ih.mpr hp) hc).mpr ht⟩

theorem same_meet (core : List A → A → Prop) (tag : List A → A → Option (I × Nat))
    (e f : I → Nat) (same : ∀ w, Good core tag e w ↔ Good core tag f w) :
    ∀ w, Good core tag e w ↔ Good core tag (fun i => min (e i) (f i)) w := by
  apply (same_iff_frontier core tag e _).mpr
  intro p a hp hc
  have h := (same_iff_frontier core tag e f).mp same p a hp hc
  cases he : tag p a with
  | none => simp [Pass]
  | some pair =>
    obtain ⟨i,t⟩ := pair
    rw [he] at h
    simp only [Pass, min_le_iff] at h ⊢
    exact ⟨Or.inl, fun hh => hh.elim id h.mpr⟩

def Both (a b : Nat) : Prop := a ≤ 0 ∧ b ≤ 0

theorem atomic_refusal_not_meet_closed :
    ¬ Both 0 1 ∧ ¬ Both 1 0 ∧ Both (min 0 1) (min 1 0) := by
  unfold Both
  decide

#print axioms same_iff_frontier
#print axioms same_meet
#print axioms atomic_refusal_not_meet_closed

end ExpiryFibres
