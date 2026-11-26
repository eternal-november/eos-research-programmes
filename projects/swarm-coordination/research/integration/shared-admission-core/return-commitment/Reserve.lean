import Lean
namespace ReserveCut

inductive Choice where
  | direct | returnNow | reserve
deriving DecidableEq

def Feasible (paid : Bool) : Choice → Prop
  | .direct => paid=true
  | .returnNow => False
  | .reserve => True

def Stage : Choice → Nat
  | .reserve => 1
  | _ => 0

theorem common_use_forced (c : Choice) (h : Feasible false c) :
    c=Choice.reserve ∧ Stage c=1 := by
  cases c <;> simp [Feasible,Stage] at *

theorem qualified_optimum :
    ∃ f : Bool → Choice, (∀ b, Feasible b (f b)) ∧
      ∀ b c, Feasible b c → Stage (f b) ≤ Stage c := by
  refine ⟨fun b => if b then .direct else .reserve, ?_, ?_⟩
  · intro b
    cases b <;> simp [Feasible]
  · intro b c h
    cases b
    · have eq := (common_use_forced c h).1
      subst c
      decide
    · cases c <;> decide

theorem same_view_no_saving {O : Type} (f : O → Choice) (old new : O) (h : old = new)
    (service : Feasible false (f old)) : Stage (f new)=1 := by
  rw [←h]
  exact (common_use_forced _ service).2

#print axioms common_use_forced
#print axioms qualified_optimum
#print axioms same_view_no_saving
end ReserveCut
