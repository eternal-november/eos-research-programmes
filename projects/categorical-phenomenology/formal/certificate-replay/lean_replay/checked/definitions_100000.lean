-- Generated mechanically from a stored certificate bundle. Do not hand-edit.
-- Source bundle SHA256: 2c26ae9f1d550f7354bd15448266de97833b10d32977f10c2174413117f51d9a
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

-- Source held-out entry: app_nil_def
theorem held_app_nil_def (v_X : List α) : (app ([] : List α) v_X) = v_X := by
  -- app_nil, direction 1, AST path []
  have left_000 : (app ([] : List α) v_X) = v_X := (app_nil (α := α) (v_Y := v_X))
  exact Eq.trans (Eq.trans left_000 (Eq.refl v_X)) (Eq.symm (Eq.refl v_X))

-- Source held-out entry: app_cons_def
theorem held_app_cons_def (e_a : α) (v_X : List α) (v_Y : List α) : (app (List.cons e_a v_X) v_Y) = (List.cons e_a (app v_X v_Y)) := by
  -- app_cons, direction 1, AST path []
  have left_000 : (app (List.cons e_a v_X) v_Y) = (List.cons e_a (app v_X v_Y)) := (app_cons (α := α) (e_a := e_a) (v_X := v_X) (v_Y := v_Y))
  exact Eq.trans (Eq.trans left_000 (Eq.refl (List.cons e_a (app v_X v_Y)))) (Eq.symm (Eq.refl (List.cons e_a (app v_X v_Y))))

-- Source held-out entry: app_two_cons_def
theorem held_app_two_cons_def (e_a : α) (e_b : α) (v_X : List α) (v_Y : List α) : (app (List.cons e_a (List.cons e_b v_X)) v_Y) = (List.cons e_a (List.cons e_b (app v_X v_Y))) := by
  -- app_cons, direction 1, AST path []
  have left_000 : (app (List.cons e_a (List.cons e_b v_X)) v_Y) = (List.cons e_a (app (List.cons e_b v_X) v_Y)) := (app_cons (α := α) (e_a := e_a) (v_X := (List.cons e_b v_X)) (v_Y := v_Y))
  -- app_cons, direction 1, AST path [2]
  have left_001 : (List.cons e_a (app (List.cons e_b v_X) v_Y)) = (List.cons e_a (List.cons e_b (app v_X v_Y))) := (congrArg (fun (replay_hole : List α) => (List.cons e_a replay_hole)) (app_cons (α := α) (e_a := e_b) (v_X := v_X) (v_Y := v_Y)))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.refl (List.cons e_a (List.cons e_b (app v_X v_Y)))))) (Eq.symm (Eq.refl (List.cons e_a (List.cons e_b (app v_X v_Y)))))

-- Source held-out entry: app_nil_nested
theorem held_app_nil_nested (v_X : List α) : (app ([] : List α) (app ([] : List α) v_X)) = v_X := by
  -- app_nil, direction 1, AST path [2]
  have left_000 : (app ([] : List α) (app ([] : List α) v_X)) = (app ([] : List α) v_X) := (congrArg (fun (replay_hole : List α) => (app ([] : List α) replay_hole)) (app_nil (α := α) (v_Y := v_X)))
  -- app_nil, direction 1, AST path []
  have left_001 : (app ([] : List α) v_X) = v_X := (app_nil (α := α) (v_Y := v_X))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.refl v_X))) (Eq.symm (Eq.refl v_X))

-- Source held-out entry: app_cons_nil_def
theorem held_app_cons_nil_def (e_a : α) (v_Y : List α) : (app (List.cons e_a ([] : List α)) v_Y) = (List.cons e_a v_Y) := by
  -- app_cons, direction 1, AST path []
  have left_000 : (app (List.cons e_a ([] : List α)) v_Y) = (List.cons e_a (app ([] : List α) v_Y)) := (app_cons (α := α) (e_a := e_a) (v_X := ([] : List α)) (v_Y := v_Y))
  -- app_nil, direction 1, AST path [2]
  have left_001 : (List.cons e_a (app ([] : List α) v_Y)) = (List.cons e_a v_Y) := (congrArg (fun (replay_hole : List α) => (List.cons e_a replay_hole)) (app_nil (α := α) (v_Y := v_Y)))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.refl (List.cons e_a v_Y)))) (Eq.symm (Eq.refl (List.cons e_a v_Y)))

-- Source held-out entry: rev_cons_nil_def
theorem held_rev_cons_nil_def (e_a : α) : (rev (List.cons e_a ([] : List α))) = (List.cons e_a ([] : List α)) := by
  -- rev_cons, direction 1, AST path []
  have left_000 : (rev (List.cons e_a ([] : List α))) = (app (rev ([] : List α)) (List.cons e_a ([] : List α))) := (rev_cons (α := α) (e_a := e_a) (v_X := ([] : List α)))
  -- rev_nil, direction 1, AST path [1]
  have left_001 : (app (rev ([] : List α)) (List.cons e_a ([] : List α))) = (app ([] : List α) (List.cons e_a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (List.cons e_a ([] : List α)))) (rev_nil (α := α)))
  -- app_nil, direction 1, AST path []
  have left_002 : (app ([] : List α) (List.cons e_a ([] : List α))) = (List.cons e_a ([] : List α)) := (app_nil (α := α) (v_Y := (List.cons e_a ([] : List α))))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.refl (List.cons e_a ([] : List α)))))) (Eq.symm (Eq.refl (List.cons e_a ([] : List α))))

-- Source held-out entry: rev_two_cons_def
theorem held_rev_two_cons_def (e_a : α) (e_b : α) : (rev (List.cons e_a (List.cons e_b ([] : List α)))) = (List.cons e_b (List.cons e_a ([] : List α))) := by
  -- rev_cons, direction 1, AST path []
  have left_000 : (rev (List.cons e_a (List.cons e_b ([] : List α)))) = (app (rev (List.cons e_b ([] : List α))) (List.cons e_a ([] : List α))) := (rev_cons (α := α) (e_a := e_a) (v_X := (List.cons e_b ([] : List α))))
  -- rev_cons, direction 1, AST path [1]
  have left_001 : (app (rev (List.cons e_b ([] : List α))) (List.cons e_a ([] : List α))) = (app (app (rev ([] : List α)) (List.cons e_b ([] : List α))) (List.cons e_a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (List.cons e_a ([] : List α)))) (rev_cons (α := α) (e_a := e_b) (v_X := ([] : List α))))
  -- rev_nil, direction 1, AST path [1, 1]
  have left_002 : (app (app (rev ([] : List α)) (List.cons e_b ([] : List α))) (List.cons e_a ([] : List α))) = (app (app ([] : List α) (List.cons e_b ([] : List α))) (List.cons e_a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app (app replay_hole (List.cons e_b ([] : List α))) (List.cons e_a ([] : List α)))) (rev_nil (α := α)))
  -- app_nil, direction 1, AST path [1]
  have left_003 : (app (app ([] : List α) (List.cons e_b ([] : List α))) (List.cons e_a ([] : List α))) = (app (List.cons e_b ([] : List α)) (List.cons e_a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (List.cons e_a ([] : List α)))) (app_nil (α := α) (v_Y := (List.cons e_b ([] : List α)))))
  -- app_cons, direction 1, AST path []
  have left_004 : (app (List.cons e_b ([] : List α)) (List.cons e_a ([] : List α))) = (List.cons e_b (app ([] : List α) (List.cons e_a ([] : List α)))) := (app_cons (α := α) (e_a := e_b) (v_X := ([] : List α)) (v_Y := (List.cons e_a ([] : List α))))
  -- app_nil, direction 1, AST path [2]
  have left_005 : (List.cons e_b (app ([] : List α) (List.cons e_a ([] : List α)))) = (List.cons e_b (List.cons e_a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (List.cons e_b replay_hole)) (app_nil (α := α) (v_Y := (List.cons e_a ([] : List α)))))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.trans left_004 (Eq.trans left_005 (Eq.refl (List.cons e_b (List.cons e_a ([] : List α)))))))))) (Eq.symm (Eq.refl (List.cons e_b (List.cons e_a ([] : List α)))))

-- Source held-out entry: rev_nil_def
theorem held_rev_nil_def : (rev ([] : List α)) = ([] : List α) := by
  -- rev_nil, direction 1, AST path []
  have left_000 : (rev ([] : List α)) = ([] : List α) := (rev_nil (α := α))
  exact Eq.trans (Eq.trans left_000 (Eq.refl ([] : List α))) (Eq.symm (Eq.refl ([] : List α)))

-- Kernel axiom audit: these should all report no axioms.
#print axioms held_app_nil_def
#print axioms held_app_cons_def
#print axioms held_app_two_cons_def
#print axioms held_app_nil_nested
#print axioms held_app_cons_nil_def
#print axioms held_rev_cons_nil_def
#print axioms held_rev_two_cons_def
#print axioms held_rev_nil_def
end CertificateReplay
