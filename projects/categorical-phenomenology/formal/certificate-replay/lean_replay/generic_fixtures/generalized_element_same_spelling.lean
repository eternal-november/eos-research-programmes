-- Generated mechanically from a stored certificate bundle. Do not hand-edit.
-- Source bundle SHA256: 3025d6140d6fca946caaf5a22cef2066742621e3cc9d5ea978f9e3e718e97dbd
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

-- Source held-out entry: generalized_element_same_spelling
theorem held_generalized_element_same_spelling (e_X : α) (v_X : List α) : (app v_X (List.cons e_X ([] : List α))) = (app v_X (List.cons e_X ([] : List α))) := by
  induction v_X generalizing e_X with
  | nil =>
    exact Eq.trans (Eq.refl (app ([] : List α) (List.cons e_X ([] : List α)))) (Eq.symm (Eq.refl (app ([] : List α) (List.cons e_X ([] : List α)))))
  | cons e_freshHead v_freshTail ih =>
    -- app_cons, direction 1, AST path []
    have left_000 : (app (List.cons e_freshHead v_freshTail) (List.cons e_X ([] : List α))) = (List.cons e_freshHead (app v_freshTail (List.cons e_X ([] : List α)))) := (app_cons (α := α) (e_a := e_freshHead) (v_X := v_freshTail) (v_Y := (List.cons e_X ([] : List α))))
    -- IH, direction 1, AST path [2]
    have left_001 : (List.cons e_freshHead (app v_freshTail (List.cons e_X ([] : List α)))) = (List.cons e_freshHead (app v_freshTail (List.cons e_X ([] : List α)))) := (congrArg (fun (replay_hole : List α) => (List.cons e_freshHead replay_hole)) (ih (e_X := e_X)))
    -- app_cons, direction 1, AST path []
    have right_000 : (app (List.cons e_freshHead v_freshTail) (List.cons e_X ([] : List α))) = (List.cons e_freshHead (app v_freshTail (List.cons e_X ([] : List α)))) := (app_cons (α := α) (e_a := e_freshHead) (v_X := v_freshTail) (v_Y := (List.cons e_X ([] : List α))))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.refl (List.cons e_freshHead (app v_freshTail (List.cons e_X ([] : List α))))))) (Eq.symm (Eq.trans right_000 (Eq.refl (List.cons e_freshHead (app v_freshTail (List.cons e_X ([] : List α)))))))

-- Kernel axiom audit: these should all report no axioms.
#print axioms held_generalized_element_same_spelling
end CertificateReplay
