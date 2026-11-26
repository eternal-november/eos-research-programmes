import Mathlib

structure Pipeline where
  sealed : Bool
  pre : ℕ
  post : ℕ
deriving DecidableEq

inductive Edge : Pipeline → Pipeline → Prop
  | publish (s) : Edge s s
  | enqueue (pre post) :
      Edge ⟨false, pre, post⟩ ⟨false, pre+1, post⟩
  | emit (c pre post) :
      Edge ⟨c, pre+1, post⟩ ⟨c, pre, post+1⟩
  | complete (c pre post) :
      Edge ⟨c, pre, post+1⟩ ⟨c, pre, post⟩
  | authorized_retract (pre post) :
      Edge ⟨true, pre+1, post⟩ ⟨true, pre, post⟩
  | seal (pre post) :
      Edge ⟨false, pre, post⟩ ⟨true, pre, post⟩

theorem qualified_one_step (a b : Pipeline)
    (edge : Edge a b) (closed : a = ⟨true, 0, 0⟩) :
    b = ⟨true, 0, 0⟩ := by
  cases edge <;> simp_all

theorem qualified_future (a b : Pipeline)
    (run : Relation.ReflTransGen Edge a b)
    (closed : a = ⟨true, 0, 0⟩) :
    b = ⟨true, 0, 0⟩ := by
  induction run with
  | refl => exact closed
  | tail r step ih => exact qualified_one_step _ _ step ih

#print axioms qualified_one_step
#print axioms qualified_future
