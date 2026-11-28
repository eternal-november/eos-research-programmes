import Mathlib
namespace JoinedSetter
inductive Horizontal where
  | latched (epoch : Nat) (x : Int)
  | authorizedStop
  deriving DecidableEq

def permitted (current : Nat) (canStop : Prop) : Horizontal → Prop
  | .latched e _ => e = current
  | .authorizedStop => canStop

def seed (current : Nat) (canStop : Bool) (e : Nat) (x : Int) : Option Horizontal :=
  if e = current then some (.latched e x)
  else if canStop then some .authorizedStop else none

theorem sound {g e : Nat} {x : Int} {q : Bool} {h : Horizontal}
    (hs : seed g q e x = some h) : permitted g (q = true) h := by
  by_cases a : e = g
  · simp [seed,a] at hs
    subst h
    simp [permitted]
  · cases q with
    | false => simp [seed,a] at hs
    | true =>
        simp [seed,a] at hs
        subst h
        simp [permitted]

theorem exact_seed (g e : Nat) (x : Int) (q : Bool) :
    (∃ h, seed g q e x = some h) ↔ (e = g ∨ q = true) := by
  by_cases a : e = g <;> cases q <;> simp [seed,a]

theorem stale_zero_not_an_authorized_stop (g e : Nat) (h : e ≠ g) :
    ¬ permitted g True (.latched e 0) ∧ permitted g True .authorizedStop := by
  exact ⟨h, trivial⟩

theorem mailbox_freshness_does_not_imply_latch (g e : Nat) (h : e ≠ g) :
    permitted g False (.latched g 0) ∧ ¬ permitted g False (.latched e 0) := by
  exact ⟨rfl,h⟩

theorem preserve_vertical_iff (current latched : Nat) (stop inside feature : Bool)
    (x : Int) :
    (∃ h, seed current stop latched x = some h ∧ inside = true ∧ feature = true) ↔
      (latched = current ∨ stop = true) ∧ inside = true ∧ feature = true := by
  constructor
  · rintro ⟨h, a, b, c⟩
    exact ⟨(exact_seed current latched x stop).mp ⟨h,a⟩,b,c⟩
  · rintro ⟨a,b,c⟩
    obtain ⟨h,hh⟩ := (exact_seed current latched x stop).mpr a
    exact ⟨h,hh,b,c⟩

end JoinedSetter
