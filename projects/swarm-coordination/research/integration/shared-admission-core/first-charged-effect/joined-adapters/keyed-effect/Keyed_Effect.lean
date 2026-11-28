import Mathlib

namespace KeyedEffect

inductive Record (A : Type)
  | pending
  | resolved (value : A)

def authority {A : Type} : Record A → Bool → Bool
  | .pending, stillPossible => stillPossible
  | .resolved _, _ => true

def transact {A : Type} (existing : Record A) (effect : Option A) :
    Record A × Bool :=
  match existing, effect with
  | .resolved a, _ => (.resolved a, false)
  | .pending, none => (.pending, false)
  | .pending, some a => (.resolved a, true)

theorem retry_cannot_repeat {A : Type} (x : A) (attempt : Option A) :
    transact (.resolved x) attempt = (.resolved x, false) := rfl

theorem settle_then_retry {A : Type} (x : A) (other : Option A) :
    transact (transact Record.pending (some x)).1 other = (.resolved x, false) := rfl

theorem replay_without_movement {A : Type} (x : A) :
    authority (.resolved x) false = true ∧
    authority (Record.pending : Record A) false = false :=
  ⟨rfl,rfl⟩

end KeyedEffect
