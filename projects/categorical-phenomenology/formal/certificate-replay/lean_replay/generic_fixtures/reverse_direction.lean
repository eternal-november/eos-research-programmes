-- Generated mechanically from a stored certificate bundle. Do not hand-edit.
-- Source bundle SHA256: 79f323c9bd635db632de9a3faf34a945f9701abd9a2057c26d389c0f0cd6a8f3
-- Only the recursive definitions and equality/induction primitives are used.
import Init
set_option autoImplicit false
set_option linter.unusedVariables false
universe u
namespace CertificateReplay
variable {α : Type u}
def app : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: app xs ys
def rev : List α → List α
  | [] => []
  | x :: xs => app (rev xs) (x :: [])
theorem app_nil (v_Y : List α) : app [] v_Y = v_Y := rfl
theorem app_cons (e_a : α) (v_X v_Y : List α) :
    app (e_a :: v_X) v_Y = e_a :: app v_X v_Y := rfl
theorem rev_nil : rev ([] : List α) = [] := rfl
theorem rev_cons (e_a : α) (v_X : List α) :
    rev (e_a :: v_X) = app (rev v_X) (e_a :: []) := rfl

-- Source held-out entry: reverse_direction
theorem held_reverse_direction (v_X : List α) : v_X = (app ([] : List α) v_X) := by
  -- app_nil, direction -1, AST path []
  have left_000 : v_X = (app ([] : List α) v_X) := (Eq.symm (app_nil (α := α) (v_Y := v_X)))
  exact Eq.trans (Eq.trans left_000 (Eq.refl (app ([] : List α) v_X))) (Eq.symm (Eq.refl (app ([] : List α) v_X)))

-- Kernel axiom audit: these should all report no axioms.
#print axioms held_reverse_direction
end CertificateReplay
