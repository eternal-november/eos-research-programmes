import Mathlib
namespace ProjectedFrame
variable {V : Type}
variable (stage use : V ≃ V) (up : V)

theorem exactReuse :
    use (stage.symm up) = up ↔ stage.symm up = use.symm up := by
  constructor
  · intro h
    simpa using congrArg use.symm h
  · intro h
    rw [h, Equiv.apply_symm_apply]

def dot (p c : Fin 3 → ℚ) := ∑ i, p i * c i
def axes (j : Fin 3) : Fin 3 → ℚ := fun i => if i = j then 1 else 0

theorem dotAxis (p : Fin 3 → ℚ) (j : Fin 3) : dot p (axes j) = p j := by
  simp [dot, axes, mul_ite]

theorem projectedEquiv (p q : Fin 3 → ℚ) : (∀ c, dot p c = dot q c) ↔ p = q := by
  constructor
  · intro h
    funext j
    simpa only [dotAxis] using h (axes j)
  · intro h
    subst q
    simp

theorem fixedLocalSlot (a b slot target : ℚ) (hb : b ≠ 0)
    (h : slot = a * b) :
    a = target ↔ slot = target * b := by
  rw [h]
  constructor
  · intro e
    rw [e]
  · intro e
    exact mul_right_cancel₀ hb e
end ProjectedFrame
