-- Generated mechanically from a stored certificate bundle. Do not hand-edit.
-- Source bundle SHA256: 43627aa47b44d8f773b924b85ac06e397c648913c9e5dbb01e37707bd22a1d13
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

-- Kernel axiom audit: these should all report no axioms.
end CertificateReplay
