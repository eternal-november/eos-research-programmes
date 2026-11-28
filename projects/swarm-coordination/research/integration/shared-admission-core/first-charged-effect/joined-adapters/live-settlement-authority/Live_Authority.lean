import Mathlib
namespace LiveAuthority
structure Interface where
  State : Type
  Action : Type
  allowed : State → Action → Prop

structure Checked (A B : Interface) where
  state : A.State → B.State
  action : A.Action → B.Action
  exactly : ∀ s a, B.allowed (state s) (action a) ↔ A.allowed s a

def ident (A : Interface) : Checked A A where
  state := id
  action := id
  exactly := by intros; rfl

def compose {A B C : Interface} (f : Checked A B) (g : Checked B C) :
    Checked A C where
  state := g.state ∘ f.state
  action := g.action ∘ f.action
  exactly := by
    intros s a
    exact (g.exactly (f.state s) (f.action a)).trans (f.exactly s a)

theorem assoc {A B C D : Interface} (f : Checked A B) (g : Checked B C)
    (h : Checked C D) : compose (compose f g) h = compose f (compose g h) := rfl
theorem unit_left {A B : Interface} (f : Checked A B) :
    compose (ident A) f = f := rfl
theorem unit_right {A B : Interface} (f : Checked A B) :
    compose f (ident B) = f := rfl

theorem stale_view_cannot_settle_both {Obs Act : Type} (pick : Obs → Act)
    {left right : Obs} {a b : Act} (same : left = right) (exclusive : a ≠ b) :
    ¬ (pick left = a ∧ pick right = b) := by
  rintro ⟨ha,hb⟩
  exact exclusive (ha.symm.trans ((congrArg pick same).trans hb))

theorem grant_cost (cap : Nat) (held : 1 + 4 ≤ cap) : 4 < cap := by omega

end LiveAuthority
