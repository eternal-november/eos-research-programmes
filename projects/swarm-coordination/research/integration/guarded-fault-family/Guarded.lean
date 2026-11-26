import Lean

namespace GuardedFamily

universe u v
variable {World : Type u} {Node : Type v}

/-- No transition can switch the admitted installation halfway along a path. -/
inductive Run (root : Node → Prop) (edge : World → Node → Node → Prop)
    (w : World) : Node → Prop where
  | root {x} : root x → Run root edge w x
  | step {x y} : Run root edge w x → edge w x y → Run root edge w y

def Bad (root goal : Node → Prop) (edge : World → Node → Node → Prop)
    (w : World) : Prop := ∃ x, goal x ∧ Run root edge w x

def Screen (A : World → Prop) (root goal : Node → Prop)
    (edge : World → Node → Node → Prop) : Prop :=
  (∃ w, A w) ∧ ∀ w, A w → ¬ Bad root goal edge w

theorem extend_iff {root : Node → Prop} {edge : World → Node → Node → Prop}
    {w : World} {x : Node} :
    Run root edge w x ↔ root x ∨ ∃ y, Run root edge w y ∧ edge w y x := by
  constructor
  · intro h
    cases h with
    | root hr => exact Or.inl hr
    | step prev g => exact Or.inr ⟨_, prev, g⟩
  · intro h
    rcases h with h | ⟨_, prev, g⟩
    · exact Run.root h
    · exact Run.step prev g

theorem screen_restrict {A A' : World → Prop} {root goal : Node → Prop}
    {edge : World → Node → Node → Prop} (h : Screen A root goal edge)
    (subset : ∀ w, A' w → A w) (live : ∃ w, A' w) :
    Screen A' root goal edge :=
  ⟨live, fun w a => h.2 w (subset w a)⟩

theorem bad_monotone {root goal : Node → Prop} {E F : World → Node → Node → Prop}
    (incl : ∀ w x y, E w x y → F w x y) {w : World} :
    Bad root goal E w → Bad root goal F w := by
  rintro ⟨x, bad, reach⟩
  refine ⟨x, bad, ?_⟩
  clear bad
  induction reach with
  | root hr => exact Run.root hr
  | step prev g ih => exact Run.step ih (incl _ _ _ g)

def splice (w : Bool) (x y : Nat) : Prop :=
  (x = 0 ∧ y = 1 ∧ w = true) ∨ (x = 1 ∧ y = 2 ∧ w = false)

theorem no_fixed_splice (w : Bool) :
    ¬Run (fun x : Nat => x = 0) splice w 2 := by
  intro h
  rcases extend_iff.mp h with h | ⟨y, prev, h0⟩
  · omega
  · rcases h0 with ⟨a,b,c⟩ | ⟨a,b,c⟩
    · omega
    · subst y
      rcases extend_iff.mp prev with h | ⟨z, prior, h1⟩
      · omega
      · rcases h1 with ⟨a,b,d⟩ | ⟨a,b,d⟩
        · simp [c] at d
        · omega

theorem union_splices :
    Run (fun x : Nat => x = 0) (fun (_ : Unit) x y => ∃ w, splice w x y) () 2 :=
  Run.step (Run.step (Run.root rfl) ⟨true, Or.inl ⟨rfl,rfl,rfl⟩⟩)
    ⟨false, Or.inr ⟨rfl,rfl,rfl⟩⟩

#print axioms extend_iff
#print axioms screen_restrict
#print axioms bad_monotone
#print axioms no_fixed_splice
#print axioms union_splices

end GuardedFamily
