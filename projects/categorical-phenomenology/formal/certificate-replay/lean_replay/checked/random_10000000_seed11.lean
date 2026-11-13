-- Generated mechanically from a stored certificate bundle. Do not hand-edit.
-- Source bundle SHA256: 879d68dcb8d493478baf66518a5dfa8c26aa4c162ea2a8dadd8a86aad8cd3b61
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

-- Source library entry: lemma_000
theorem lib_lemma_000 (v_X : List α) (v_Y : List α) : (app (app v_X v_Y) ([] : List α)) = (app v_X (app v_Y ([] : List α))) := by
  induction v_X generalizing v_Y with
  | nil =>
    -- app_nil, direction 1, AST path [1]
    have left_000 : (app (app ([] : List α) v_Y) ([] : List α)) = (app v_Y ([] : List α)) := (congrArg (fun (replay_hole : List α) => (app replay_hole ([] : List α))) (app_nil (α := α) (v_Y := v_Y)))
    -- app_nil, direction 1, AST path []
    have right_000 : (app ([] : List α) (app v_Y ([] : List α))) = (app v_Y ([] : List α)) := (app_nil (α := α) (v_Y := (app v_Y ([] : List α))))
    exact Eq.trans (Eq.trans left_000 (Eq.refl (app v_Y ([] : List α)))) (Eq.symm (Eq.trans right_000 (Eq.refl (app v_Y ([] : List α)))))
  | cons e__a v__t ih =>
    -- app_cons, direction 1, AST path [1]
    have left_000 : (app (app (List.cons e__a v__t) v_Y) ([] : List α)) = (app (List.cons e__a (app v__t v_Y)) ([] : List α)) := (congrArg (fun (replay_hole : List α) => (app replay_hole ([] : List α))) (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := v_Y)))
    -- app_cons, direction 1, AST path []
    have left_001 : (app (List.cons e__a (app v__t v_Y)) ([] : List α)) = (List.cons e__a (app (app v__t v_Y) ([] : List α))) := (app_cons (α := α) (e_a := e__a) (v_X := (app v__t v_Y)) (v_Y := ([] : List α)))
    -- IH, direction 1, AST path [2]
    have left_002 : (List.cons e__a (app (app v__t v_Y) ([] : List α))) = (List.cons e__a (app v__t (app v_Y ([] : List α)))) := (congrArg (fun (replay_hole : List α) => (List.cons e__a replay_hole)) (ih (v_Y := v_Y)))
    -- app_cons, direction 1, AST path []
    have right_000 : (app (List.cons e__a v__t) (app v_Y ([] : List α))) = (List.cons e__a (app v__t (app v_Y ([] : List α)))) := (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := (app v_Y ([] : List α))))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.refl (List.cons e__a (app v__t (app v_Y ([] : List α)))))))) (Eq.symm (Eq.trans right_000 (Eq.refl (List.cons e__a (app v__t (app v_Y ([] : List α)))))))

-- Source library entry: lemma_001
theorem lib_lemma_001 (v_X : List α) (v_Y : List α) : (app (app v_X v_Y) v_Y) = (app v_X (app v_Y v_Y)) := by
  induction v_X generalizing v_Y with
  | nil =>
    -- app_nil, direction 1, AST path [1]
    have left_000 : (app (app ([] : List α) v_Y) v_Y) = (app v_Y v_Y) := (congrArg (fun (replay_hole : List α) => (app replay_hole v_Y)) (app_nil (α := α) (v_Y := v_Y)))
    -- app_nil, direction 1, AST path []
    have right_000 : (app ([] : List α) (app v_Y v_Y)) = (app v_Y v_Y) := (app_nil (α := α) (v_Y := (app v_Y v_Y)))
    exact Eq.trans (Eq.trans left_000 (Eq.refl (app v_Y v_Y))) (Eq.symm (Eq.trans right_000 (Eq.refl (app v_Y v_Y))))
  | cons e__a v__t ih =>
    -- app_cons, direction 1, AST path [1]
    have left_000 : (app (app (List.cons e__a v__t) v_Y) v_Y) = (app (List.cons e__a (app v__t v_Y)) v_Y) := (congrArg (fun (replay_hole : List α) => (app replay_hole v_Y)) (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := v_Y)))
    -- app_cons, direction 1, AST path []
    have left_001 : (app (List.cons e__a (app v__t v_Y)) v_Y) = (List.cons e__a (app (app v__t v_Y) v_Y)) := (app_cons (α := α) (e_a := e__a) (v_X := (app v__t v_Y)) (v_Y := v_Y))
    -- IH, direction 1, AST path [2]
    have left_002 : (List.cons e__a (app (app v__t v_Y) v_Y)) = (List.cons e__a (app v__t (app v_Y v_Y))) := (congrArg (fun (replay_hole : List α) => (List.cons e__a replay_hole)) (ih (v_Y := v_Y)))
    -- app_cons, direction 1, AST path []
    have right_000 : (app (List.cons e__a v__t) (app v_Y v_Y)) = (List.cons e__a (app v__t (app v_Y v_Y))) := (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := (app v_Y v_Y)))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.refl (List.cons e__a (app v__t (app v_Y v_Y))))))) (Eq.symm (Eq.trans right_000 (Eq.refl (List.cons e__a (app v__t (app v_Y v_Y))))))

-- Source library entry: lemma_002
theorem lib_lemma_002 (v_X : List α) (v_Y : List α) : (app (app v_X ([] : List α)) v_Y) = (app ([] : List α) (app v_X v_Y)) := by
  induction v_X generalizing v_Y with
  | nil =>
    -- app_nil, direction 1, AST path [1]
    have left_000 : (app (app ([] : List α) ([] : List α)) v_Y) = (app ([] : List α) v_Y) := (congrArg (fun (replay_hole : List α) => (app replay_hole v_Y)) (app_nil (α := α) (v_Y := ([] : List α))))
    -- app_nil, direction 1, AST path []
    have left_001 : (app ([] : List α) v_Y) = v_Y := (app_nil (α := α) (v_Y := v_Y))
    -- app_nil, direction 1, AST path [2]
    have right_000 : (app ([] : List α) (app ([] : List α) v_Y)) = (app ([] : List α) v_Y) := (congrArg (fun (replay_hole : List α) => (app ([] : List α) replay_hole)) (app_nil (α := α) (v_Y := v_Y)))
    -- app_nil, direction 1, AST path []
    have right_001 : (app ([] : List α) v_Y) = v_Y := (app_nil (α := α) (v_Y := v_Y))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.refl v_Y))) (Eq.symm (Eq.trans right_000 (Eq.trans right_001 (Eq.refl v_Y))))
  | cons e__a v__t ih =>
    -- app_cons, direction 1, AST path [1]
    have left_000 : (app (app (List.cons e__a v__t) ([] : List α)) v_Y) = (app (List.cons e__a (app v__t ([] : List α))) v_Y) := (congrArg (fun (replay_hole : List α) => (app replay_hole v_Y)) (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := ([] : List α))))
    -- app_cons, direction 1, AST path []
    have left_001 : (app (List.cons e__a (app v__t ([] : List α))) v_Y) = (List.cons e__a (app (app v__t ([] : List α)) v_Y)) := (app_cons (α := α) (e_a := e__a) (v_X := (app v__t ([] : List α))) (v_Y := v_Y))
    -- IH, direction 1, AST path [2]
    have left_002 : (List.cons e__a (app (app v__t ([] : List α)) v_Y)) = (List.cons e__a (app ([] : List α) (app v__t v_Y))) := (congrArg (fun (replay_hole : List α) => (List.cons e__a replay_hole)) (ih (v_Y := v_Y)))
    -- app_nil, direction 1, AST path [2]
    have left_003 : (List.cons e__a (app ([] : List α) (app v__t v_Y))) = (List.cons e__a (app v__t v_Y)) := (congrArg (fun (replay_hole : List α) => (List.cons e__a replay_hole)) (app_nil (α := α) (v_Y := (app v__t v_Y))))
    -- app_cons, direction 1, AST path [2]
    have right_000 : (app ([] : List α) (app (List.cons e__a v__t) v_Y)) = (app ([] : List α) (List.cons e__a (app v__t v_Y))) := (congrArg (fun (replay_hole : List α) => (app ([] : List α) replay_hole)) (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := v_Y)))
    -- app_nil, direction 1, AST path []
    have right_001 : (app ([] : List α) (List.cons e__a (app v__t v_Y))) = (List.cons e__a (app v__t v_Y)) := (app_nil (α := α) (v_Y := (List.cons e__a (app v__t v_Y))))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.refl (List.cons e__a (app v__t v_Y))))))) (Eq.symm (Eq.trans right_000 (Eq.trans right_001 (Eq.refl (List.cons e__a (app v__t v_Y))))))

-- Source library entry: lemma_003
theorem lib_lemma_003 (v_X : List α) : (rev (app v_X ([] : List α))) = (rev v_X) := by
  induction v_X with
  | nil =>
    -- app_nil, direction 1, AST path [1]
    have left_000 : (rev (app ([] : List α) ([] : List α))) = (rev ([] : List α)) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (app_nil (α := α) (v_Y := ([] : List α))))
    -- rev_nil, direction 1, AST path []
    have left_001 : (rev ([] : List α)) = ([] : List α) := (rev_nil (α := α))
    -- rev_nil, direction 1, AST path []
    have right_000 : (rev ([] : List α)) = ([] : List α) := (rev_nil (α := α))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.refl ([] : List α)))) (Eq.symm (Eq.trans right_000 (Eq.refl ([] : List α))))
  | cons e__a v__t ih =>
    -- app_cons, direction 1, AST path [1]
    have left_000 : (rev (app (List.cons e__a v__t) ([] : List α))) = (rev (List.cons e__a (app v__t ([] : List α)))) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := ([] : List α))))
    -- rev_cons, direction 1, AST path []
    have left_001 : (rev (List.cons e__a (app v__t ([] : List α)))) = (app (rev (app v__t ([] : List α))) (List.cons e__a ([] : List α))) := (rev_cons (α := α) (e_a := e__a) (v_X := (app v__t ([] : List α))))
    -- IH, direction 1, AST path [1]
    have left_002 : (app (rev (app v__t ([] : List α))) (List.cons e__a ([] : List α))) = (app (rev v__t) (List.cons e__a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (List.cons e__a ([] : List α)))) (ih))
    -- rev_cons, direction 1, AST path []
    have right_000 : (rev (List.cons e__a v__t)) = (app (rev v__t) (List.cons e__a ([] : List α))) := (rev_cons (α := α) (e_a := e__a) (v_X := v__t))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.refl (app (rev v__t) (List.cons e__a ([] : List α))))))) (Eq.symm (Eq.trans right_000 (Eq.refl (app (rev v__t) (List.cons e__a ([] : List α))))))

-- Source library entry: lemma_004
theorem lib_lemma_004 (v_X : List α) : (app (rev v_X) (rev ([] : List α))) = (rev v_X) := by
  induction v_X with
  | nil =>
    -- rev_nil, direction 1, AST path [1]
    have left_000 : (app (rev ([] : List α)) (rev ([] : List α))) = (app ([] : List α) (rev ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev ([] : List α)))) (rev_nil (α := α)))
    -- rev_nil, direction 1, AST path [2]
    have left_001 : (app ([] : List α) (rev ([] : List α))) = (app ([] : List α) ([] : List α)) := (congrArg (fun (replay_hole : List α) => (app ([] : List α) replay_hole)) (rev_nil (α := α)))
    -- app_nil, direction 1, AST path []
    have left_002 : (app ([] : List α) ([] : List α)) = ([] : List α) := (app_nil (α := α) (v_Y := ([] : List α)))
    -- rev_nil, direction 1, AST path []
    have right_000 : (rev ([] : List α)) = ([] : List α) := (rev_nil (α := α))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.refl ([] : List α))))) (Eq.symm (Eq.trans right_000 (Eq.refl ([] : List α))))
  | cons e__a v__t ih =>
    -- rev_cons, direction 1, AST path [1]
    have left_000 : (app (rev (List.cons e__a v__t)) (rev ([] : List α))) = (app (app (rev v__t) (List.cons e__a ([] : List α))) (rev ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev ([] : List α)))) (rev_cons (α := α) (e_a := e__a) (v_X := v__t)))
    -- rev_nil, direction 1, AST path [2]
    have left_001 : (app (app (rev v__t) (List.cons e__a ([] : List α))) (rev ([] : List α))) = (app (app (rev v__t) (List.cons e__a ([] : List α))) ([] : List α)) := (congrArg (fun (replay_hole : List α) => (app (app (rev v__t) (List.cons e__a ([] : List α))) replay_hole)) (rev_nil (α := α)))
    -- lemma_000, direction 1, AST path []
    have left_002 : (app (app (rev v__t) (List.cons e__a ([] : List α))) ([] : List α)) = (app (rev v__t) (app (List.cons e__a ([] : List α)) ([] : List α))) := (lib_lemma_000 (α := α) (v_X := (rev v__t)) (v_Y := (List.cons e__a ([] : List α))))
    -- app_cons, direction 1, AST path [2]
    have left_003 : (app (rev v__t) (app (List.cons e__a ([] : List α)) ([] : List α))) = (app (rev v__t) (List.cons e__a (app ([] : List α) ([] : List α)))) := (congrArg (fun (replay_hole : List α) => (app (rev v__t) replay_hole)) (app_cons (α := α) (e_a := e__a) (v_X := ([] : List α)) (v_Y := ([] : List α))))
    -- app_nil, direction 1, AST path [2, 2]
    have left_004 : (app (rev v__t) (List.cons e__a (app ([] : List α) ([] : List α)))) = (app (rev v__t) (List.cons e__a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app (rev v__t) (List.cons e__a replay_hole))) (app_nil (α := α) (v_Y := ([] : List α))))
    -- rev_cons, direction 1, AST path []
    have right_000 : (rev (List.cons e__a v__t)) = (app (rev v__t) (List.cons e__a ([] : List α))) := (rev_cons (α := α) (e_a := e__a) (v_X := v__t))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.trans left_004 (Eq.refl (app (rev v__t) (List.cons e__a ([] : List α))))))))) (Eq.symm (Eq.trans right_000 (Eq.refl (app (rev v__t) (List.cons e__a ([] : List α))))))

-- Source library entry: lemma_005
theorem lib_lemma_005 (v_X : List α) : (rev (app v_X (rev ([] : List α)))) = (app (rev v_X) ([] : List α)) := by
  induction v_X with
  | nil =>
    -- rev_nil, direction 1, AST path [1, 2]
    have left_000 : (rev (app ([] : List α) (rev ([] : List α)))) = (rev (app ([] : List α) ([] : List α))) := (congrArg (fun (replay_hole : List α) => (rev (app ([] : List α) replay_hole))) (rev_nil (α := α)))
    -- app_nil, direction 1, AST path [1]
    have left_001 : (rev (app ([] : List α) ([] : List α))) = (rev ([] : List α)) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (app_nil (α := α) (v_Y := ([] : List α))))
    -- rev_nil, direction 1, AST path []
    have left_002 : (rev ([] : List α)) = ([] : List α) := (rev_nil (α := α))
    -- rev_nil, direction 1, AST path [1]
    have right_000 : (app (rev ([] : List α)) ([] : List α)) = (app ([] : List α) ([] : List α)) := (congrArg (fun (replay_hole : List α) => (app replay_hole ([] : List α))) (rev_nil (α := α)))
    -- app_nil, direction 1, AST path []
    have right_001 : (app ([] : List α) ([] : List α)) = ([] : List α) := (app_nil (α := α) (v_Y := ([] : List α)))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.refl ([] : List α))))) (Eq.symm (Eq.trans right_000 (Eq.trans right_001 (Eq.refl ([] : List α)))))
  | cons e__a v__t ih =>
    -- rev_nil, direction 1, AST path [1, 2]
    have left_000 : (rev (app (List.cons e__a v__t) (rev ([] : List α)))) = (rev (app (List.cons e__a v__t) ([] : List α))) := (congrArg (fun (replay_hole : List α) => (rev (app (List.cons e__a v__t) replay_hole))) (rev_nil (α := α)))
    -- app_cons, direction 1, AST path [1]
    have left_001 : (rev (app (List.cons e__a v__t) ([] : List α))) = (rev (List.cons e__a (app v__t ([] : List α)))) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := ([] : List α))))
    -- rev_cons, direction 1, AST path []
    have left_002 : (rev (List.cons e__a (app v__t ([] : List α)))) = (app (rev (app v__t ([] : List α))) (List.cons e__a ([] : List α))) := (rev_cons (α := α) (e_a := e__a) (v_X := (app v__t ([] : List α))))
    -- lemma_003, direction 1, AST path [1]
    have left_003 : (app (rev (app v__t ([] : List α))) (List.cons e__a ([] : List α))) = (app (rev v__t) (List.cons e__a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (List.cons e__a ([] : List α)))) (lib_lemma_003 (α := α) (v_X := v__t)))
    -- rev_cons, direction 1, AST path [1]
    have right_000 : (app (rev (List.cons e__a v__t)) ([] : List α)) = (app (app (rev v__t) (List.cons e__a ([] : List α))) ([] : List α)) := (congrArg (fun (replay_hole : List α) => (app replay_hole ([] : List α))) (rev_cons (α := α) (e_a := e__a) (v_X := v__t)))
    -- lemma_000, direction 1, AST path []
    have right_001 : (app (app (rev v__t) (List.cons e__a ([] : List α))) ([] : List α)) = (app (rev v__t) (app (List.cons e__a ([] : List α)) ([] : List α))) := (lib_lemma_000 (α := α) (v_X := (rev v__t)) (v_Y := (List.cons e__a ([] : List α))))
    -- app_cons, direction 1, AST path [2]
    have right_002 : (app (rev v__t) (app (List.cons e__a ([] : List α)) ([] : List α))) = (app (rev v__t) (List.cons e__a (app ([] : List α) ([] : List α)))) := (congrArg (fun (replay_hole : List α) => (app (rev v__t) replay_hole)) (app_cons (α := α) (e_a := e__a) (v_X := ([] : List α)) (v_Y := ([] : List α))))
    -- app_nil, direction 1, AST path [2, 2]
    have right_003 : (app (rev v__t) (List.cons e__a (app ([] : List α) ([] : List α)))) = (app (rev v__t) (List.cons e__a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app (rev v__t) (List.cons e__a replay_hole))) (app_nil (α := α) (v_Y := ([] : List α))))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.refl (app (rev v__t) (List.cons e__a ([] : List α)))))))) (Eq.symm (Eq.trans right_000 (Eq.trans right_001 (Eq.trans right_002 (Eq.trans right_003 (Eq.refl (app (rev v__t) (List.cons e__a ([] : List α)))))))))

-- Source library entry: lemma_006
theorem lib_lemma_006 (v_X : List α) : (app v_X ([] : List α)) = v_X := by
  induction v_X with
  | nil =>
    -- app_nil, direction 1, AST path []
    have left_000 : (app ([] : List α) ([] : List α)) = ([] : List α) := (app_nil (α := α) (v_Y := ([] : List α)))
    exact Eq.trans (Eq.trans left_000 (Eq.refl ([] : List α))) (Eq.symm (Eq.refl ([] : List α)))
  | cons e__a v__t ih =>
    -- app_cons, direction 1, AST path []
    have left_000 : (app (List.cons e__a v__t) ([] : List α)) = (List.cons e__a (app v__t ([] : List α))) := (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := ([] : List α)))
    -- IH, direction 1, AST path [2]
    have left_001 : (List.cons e__a (app v__t ([] : List α))) = (List.cons e__a v__t) := (congrArg (fun (replay_hole : List α) => (List.cons e__a replay_hole)) (ih))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.refl (List.cons e__a v__t)))) (Eq.symm (Eq.refl (List.cons e__a v__t)))

-- Source library entry: lemma_007
theorem lib_lemma_007 (v_X : List α) (v_Y : List α) (v_Z : List α) : (app (app v_X v_Y) v_Z) = (app v_X (app v_Y v_Z)) := by
  induction v_X generalizing v_Y v_Z with
  | nil =>
    -- app_nil, direction 1, AST path [1]
    have left_000 : (app (app ([] : List α) v_Y) v_Z) = (app v_Y v_Z) := (congrArg (fun (replay_hole : List α) => (app replay_hole v_Z)) (app_nil (α := α) (v_Y := v_Y)))
    -- app_nil, direction 1, AST path []
    have right_000 : (app ([] : List α) (app v_Y v_Z)) = (app v_Y v_Z) := (app_nil (α := α) (v_Y := (app v_Y v_Z)))
    exact Eq.trans (Eq.trans left_000 (Eq.refl (app v_Y v_Z))) (Eq.symm (Eq.trans right_000 (Eq.refl (app v_Y v_Z))))
  | cons e__a v__t ih =>
    -- app_cons, direction 1, AST path [1]
    have left_000 : (app (app (List.cons e__a v__t) v_Y) v_Z) = (app (List.cons e__a (app v__t v_Y)) v_Z) := (congrArg (fun (replay_hole : List α) => (app replay_hole v_Z)) (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := v_Y)))
    -- app_cons, direction 1, AST path []
    have left_001 : (app (List.cons e__a (app v__t v_Y)) v_Z) = (List.cons e__a (app (app v__t v_Y) v_Z)) := (app_cons (α := α) (e_a := e__a) (v_X := (app v__t v_Y)) (v_Y := v_Z))
    -- IH, direction 1, AST path [2]
    have left_002 : (List.cons e__a (app (app v__t v_Y) v_Z)) = (List.cons e__a (app v__t (app v_Y v_Z))) := (congrArg (fun (replay_hole : List α) => (List.cons e__a replay_hole)) (ih (v_Y := v_Y) (v_Z := v_Z)))
    -- app_cons, direction 1, AST path []
    have right_000 : (app (List.cons e__a v__t) (app v_Y v_Z)) = (List.cons e__a (app v__t (app v_Y v_Z))) := (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := (app v_Y v_Z)))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.refl (List.cons e__a (app v__t (app v_Y v_Z))))))) (Eq.symm (Eq.trans right_000 (Eq.refl (List.cons e__a (app v__t (app v_Y v_Z))))))

-- Source library entry: lemma_008
theorem lib_lemma_008 (v_X : List α) (v_Y : List α) : (rev (app v_X v_Y)) = (app (rev v_Y) (rev v_X)) := by
  induction v_X generalizing v_Y with
  | nil =>
    -- app_nil, direction 1, AST path [1]
    have left_000 : (rev (app ([] : List α) v_Y)) = (rev v_Y) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (app_nil (α := α) (v_Y := v_Y)))
    -- rev_nil, direction 1, AST path [2]
    have right_000 : (app (rev v_Y) (rev ([] : List α))) = (app (rev v_Y) ([] : List α)) := (congrArg (fun (replay_hole : List α) => (app (rev v_Y) replay_hole)) (rev_nil (α := α)))
    -- lemma_006, direction 1, AST path []
    have right_001 : (app (rev v_Y) ([] : List α)) = (rev v_Y) := (lib_lemma_006 (α := α) (v_X := (rev v_Y)))
    exact Eq.trans (Eq.trans left_000 (Eq.refl (rev v_Y))) (Eq.symm (Eq.trans right_000 (Eq.trans right_001 (Eq.refl (rev v_Y)))))
  | cons e__a v__t ih =>
    -- app_cons, direction 1, AST path [1]
    have left_000 : (rev (app (List.cons e__a v__t) v_Y)) = (rev (List.cons e__a (app v__t v_Y))) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (app_cons (α := α) (e_a := e__a) (v_X := v__t) (v_Y := v_Y)))
    -- rev_cons, direction 1, AST path []
    have left_001 : (rev (List.cons e__a (app v__t v_Y))) = (app (rev (app v__t v_Y)) (List.cons e__a ([] : List α))) := (rev_cons (α := α) (e_a := e__a) (v_X := (app v__t v_Y)))
    -- IH, direction 1, AST path [1]
    have left_002 : (app (rev (app v__t v_Y)) (List.cons e__a ([] : List α))) = (app (app (rev v_Y) (rev v__t)) (List.cons e__a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (List.cons e__a ([] : List α)))) (ih (v_Y := v_Y)))
    -- lemma_007, direction 1, AST path []
    have left_003 : (app (app (rev v_Y) (rev v__t)) (List.cons e__a ([] : List α))) = (app (rev v_Y) (app (rev v__t) (List.cons e__a ([] : List α)))) := (lib_lemma_007 (α := α) (v_X := (rev v_Y)) (v_Y := (rev v__t)) (v_Z := (List.cons e__a ([] : List α))))
    -- rev_cons, direction 1, AST path [2]
    have right_000 : (app (rev v_Y) (rev (List.cons e__a v__t))) = (app (rev v_Y) (app (rev v__t) (List.cons e__a ([] : List α)))) := (congrArg (fun (replay_hole : List α) => (app (rev v_Y) replay_hole)) (rev_cons (α := α) (e_a := e__a) (v_X := v__t)))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.refl (app (rev v_Y) (app (rev v__t) (List.cons e__a ([] : List α))))))))) (Eq.symm (Eq.trans right_000 (Eq.refl (app (rev v_Y) (app (rev v__t) (List.cons e__a ([] : List α)))))))

-- Source library entry: training_cached
theorem lib_training_cached (v_X : List α) : (rev (rev v_X)) = v_X := by
  induction v_X with
  | nil =>
    -- rev_nil, direction 1, AST path [1]
    have left_000 : (rev (rev ([] : List α))) = (rev ([] : List α)) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (rev_nil (α := α)))
    -- rev_nil, direction 1, AST path []
    have left_001 : (rev ([] : List α)) = ([] : List α) := (rev_nil (α := α))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.refl ([] : List α)))) (Eq.symm (Eq.refl ([] : List α)))
  | cons e__a v__t ih =>
    -- rev_cons, direction 1, AST path [1]
    have left_000 : (rev (rev (List.cons e__a v__t))) = (rev (app (rev v__t) (List.cons e__a ([] : List α)))) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (rev_cons (α := α) (e_a := e__a) (v_X := v__t)))
    -- lemma_008, direction 1, AST path []
    have left_001 : (rev (app (rev v__t) (List.cons e__a ([] : List α)))) = (app (rev (List.cons e__a ([] : List α))) (rev (rev v__t))) := (lib_lemma_008 (α := α) (v_X := (rev v__t)) (v_Y := (List.cons e__a ([] : List α))))
    -- rev_cons, direction 1, AST path [1]
    have left_002 : (app (rev (List.cons e__a ([] : List α))) (rev (rev v__t))) = (app (app (rev ([] : List α)) (List.cons e__a ([] : List α))) (rev (rev v__t))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev (rev v__t)))) (rev_cons (α := α) (e_a := e__a) (v_X := ([] : List α))))
    -- rev_nil, direction 1, AST path [1, 1]
    have left_003 : (app (app (rev ([] : List α)) (List.cons e__a ([] : List α))) (rev (rev v__t))) = (app (app ([] : List α) (List.cons e__a ([] : List α))) (rev (rev v__t))) := (congrArg (fun (replay_hole : List α) => (app (app replay_hole (List.cons e__a ([] : List α))) (rev (rev v__t)))) (rev_nil (α := α)))
    -- app_nil, direction 1, AST path [1]
    have left_004 : (app (app ([] : List α) (List.cons e__a ([] : List α))) (rev (rev v__t))) = (app (List.cons e__a ([] : List α)) (rev (rev v__t))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev (rev v__t)))) (app_nil (α := α) (v_Y := (List.cons e__a ([] : List α)))))
    -- IH, direction 1, AST path [2]
    have left_005 : (app (List.cons e__a ([] : List α)) (rev (rev v__t))) = (app (List.cons e__a ([] : List α)) v__t) := (congrArg (fun (replay_hole : List α) => (app (List.cons e__a ([] : List α)) replay_hole)) (ih))
    -- app_cons, direction 1, AST path []
    have left_006 : (app (List.cons e__a ([] : List α)) v__t) = (List.cons e__a (app ([] : List α) v__t)) := (app_cons (α := α) (e_a := e__a) (v_X := ([] : List α)) (v_Y := v__t))
    -- app_nil, direction 1, AST path [2]
    have left_007 : (List.cons e__a (app ([] : List α) v__t)) = (List.cons e__a v__t) := (congrArg (fun (replay_hole : List α) => (List.cons e__a replay_hole)) (app_nil (α := α) (v_Y := v__t)))
    exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.trans left_004 (Eq.trans left_005 (Eq.trans left_006 (Eq.trans left_007 (Eq.refl (List.cons e__a v__t)))))))))) (Eq.symm (Eq.refl (List.cons e__a v__t)))

-- Source held-out entry: rev_app
theorem held_rev_app (v_X : List α) (v_Y : List α) : (rev (app v_X v_Y)) = (app (rev v_Y) (rev v_X)) := by
  -- lemma_008, direction 1, AST path []
  have left_000 : (rev (app v_X v_Y)) = (app (rev v_Y) (rev v_X)) := (lib_lemma_008 (α := α) (v_X := v_X) (v_Y := v_Y))
  exact Eq.trans (Eq.trans left_000 (Eq.refl (app (rev v_Y) (rev v_X)))) (Eq.symm (Eq.refl (app (rev v_Y) (rev v_X))))

-- Source held-out entry: rev_revapp_left
theorem held_rev_revapp_left (v_X : List α) (v_Y : List α) : (rev (app (rev v_X) v_Y)) = (app (rev v_Y) v_X) := by
  -- lemma_008, direction 1, AST path []
  have left_000 : (rev (app (rev v_X) v_Y)) = (app (rev v_Y) (rev (rev v_X))) := (lib_lemma_008 (α := α) (v_X := (rev v_X)) (v_Y := v_Y))
  -- training_cached, direction 1, AST path [2]
  have left_001 : (app (rev v_Y) (rev (rev v_X))) = (app (rev v_Y) v_X) := (congrArg (fun (replay_hole : List α) => (app (rev v_Y) replay_hole)) (lib_training_cached (α := α) (v_X := v_X)))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.refl (app (rev v_Y) v_X)))) (Eq.symm (Eq.refl (app (rev v_Y) v_X)))

-- Source held-out entry: rev_revapp_right
theorem held_rev_revapp_right (v_X : List α) (v_Y : List α) : (rev (app v_X (rev v_Y))) = (app v_Y (rev v_X)) := by
  -- lemma_008, direction 1, AST path []
  have left_000 : (rev (app v_X (rev v_Y))) = (app (rev (rev v_Y)) (rev v_X)) := (lib_lemma_008 (α := α) (v_X := v_X) (v_Y := (rev v_Y)))
  -- training_cached, direction 1, AST path [1]
  have left_001 : (app (rev (rev v_Y)) (rev v_X)) = (app v_Y (rev v_X)) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev v_X))) (lib_training_cached (α := α) (v_X := v_Y)))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.refl (app v_Y (rev v_X))))) (Eq.symm (Eq.refl (app v_Y (rev v_X))))

-- Source held-out entry: rev_three_left
theorem held_rev_three_left (v_X : List α) (v_Y : List α) (v_Z : List α) : (rev (app (app v_X v_Y) v_Z)) = (app (rev v_Z) (app (rev v_Y) (rev v_X))) := by
  -- lemma_007, direction 1, AST path [1]
  have left_000 : (rev (app (app v_X v_Y) v_Z)) = (rev (app v_X (app v_Y v_Z))) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (lib_lemma_007 (α := α) (v_X := v_X) (v_Y := v_Y) (v_Z := v_Z)))
  -- lemma_008, direction 1, AST path []
  have left_001 : (rev (app v_X (app v_Y v_Z))) = (app (rev (app v_Y v_Z)) (rev v_X)) := (lib_lemma_008 (α := α) (v_X := v_X) (v_Y := (app v_Y v_Z)))
  -- lemma_008, direction 1, AST path [1]
  have left_002 : (app (rev (app v_Y v_Z)) (rev v_X)) = (app (app (rev v_Z) (rev v_Y)) (rev v_X)) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev v_X))) (lib_lemma_008 (α := α) (v_X := v_Y) (v_Y := v_Z)))
  -- lemma_007, direction 1, AST path []
  have left_003 : (app (app (rev v_Z) (rev v_Y)) (rev v_X)) = (app (rev v_Z) (app (rev v_Y) (rev v_X))) := (lib_lemma_007 (α := α) (v_X := (rev v_Z)) (v_Y := (rev v_Y)) (v_Z := (rev v_X)))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.refl (app (rev v_Z) (app (rev v_Y) (rev v_X)))))))) (Eq.symm (Eq.refl (app (rev v_Z) (app (rev v_Y) (rev v_X)))))

-- Source held-out entry: rev_three_right
theorem held_rev_three_right (v_X : List α) (v_Y : List α) (v_Z : List α) : (rev (app v_X (app v_Y v_Z))) = (app (rev v_Z) (app (rev v_Y) (rev v_X))) := by
  -- lemma_008, direction 1, AST path []
  have left_000 : (rev (app v_X (app v_Y v_Z))) = (app (rev (app v_Y v_Z)) (rev v_X)) := (lib_lemma_008 (α := α) (v_X := v_X) (v_Y := (app v_Y v_Z)))
  -- lemma_008, direction 1, AST path [1]
  have left_001 : (app (rev (app v_Y v_Z)) (rev v_X)) = (app (app (rev v_Z) (rev v_Y)) (rev v_X)) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev v_X))) (lib_lemma_008 (α := α) (v_X := v_Y) (v_Y := v_Z)))
  -- lemma_007, direction 1, AST path []
  have left_002 : (app (app (rev v_Z) (rev v_Y)) (rev v_X)) = (app (rev v_Z) (app (rev v_Y) (rev v_X))) := (lib_lemma_007 (α := α) (v_X := (rev v_Z)) (v_Y := (rev v_Y)) (v_Z := (rev v_X)))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.refl (app (rev v_Z) (app (rev v_Y) (rev v_X))))))) (Eq.symm (Eq.refl (app (rev v_Z) (app (rev v_Y) (rev v_X)))))

-- Source held-out entry: rev_nested
theorem held_rev_nested (v_X : List α) (v_Y : List α) (v_Z : List α) : (rev (app (rev (app v_X v_Y)) v_Z)) = (app (rev v_Z) (app v_X v_Y)) := by
  -- lemma_008, direction 1, AST path [1, 1]
  have left_000 : (rev (app (rev (app v_X v_Y)) v_Z)) = (rev (app (app (rev v_Y) (rev v_X)) v_Z)) := (congrArg (fun (replay_hole : List α) => (rev (app replay_hole v_Z))) (lib_lemma_008 (α := α) (v_X := v_X) (v_Y := v_Y)))
  -- lemma_007, direction 1, AST path [1]
  have left_001 : (rev (app (app (rev v_Y) (rev v_X)) v_Z)) = (rev (app (rev v_Y) (app (rev v_X) v_Z))) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (lib_lemma_007 (α := α) (v_X := (rev v_Y)) (v_Y := (rev v_X)) (v_Z := v_Z)))
  -- lemma_008, direction 1, AST path []
  have left_002 : (rev (app (rev v_Y) (app (rev v_X) v_Z))) = (app (rev (app (rev v_X) v_Z)) (rev (rev v_Y))) := (lib_lemma_008 (α := α) (v_X := (rev v_Y)) (v_Y := (app (rev v_X) v_Z)))
  -- lemma_008, direction 1, AST path [1]
  have left_003 : (app (rev (app (rev v_X) v_Z)) (rev (rev v_Y))) = (app (app (rev v_Z) (rev (rev v_X))) (rev (rev v_Y))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev (rev v_Y)))) (lib_lemma_008 (α := α) (v_X := (rev v_X)) (v_Y := v_Z)))
  -- training_cached, direction 1, AST path [1, 2]
  have left_004 : (app (app (rev v_Z) (rev (rev v_X))) (rev (rev v_Y))) = (app (app (rev v_Z) v_X) (rev (rev v_Y))) := (congrArg (fun (replay_hole : List α) => (app (app (rev v_Z) replay_hole) (rev (rev v_Y)))) (lib_training_cached (α := α) (v_X := v_X)))
  -- training_cached, direction 1, AST path [2]
  have left_005 : (app (app (rev v_Z) v_X) (rev (rev v_Y))) = (app (app (rev v_Z) v_X) v_Y) := (congrArg (fun (replay_hole : List α) => (app (app (rev v_Z) v_X) replay_hole)) (lib_training_cached (α := α) (v_X := v_Y)))
  -- lemma_007, direction 1, AST path []
  have left_006 : (app (app (rev v_Z) v_X) v_Y) = (app (rev v_Z) (app v_X v_Y)) := (lib_lemma_007 (α := α) (v_X := (rev v_Z)) (v_Y := v_X) (v_Z := v_Y))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.trans left_004 (Eq.trans left_005 (Eq.trans left_006 (Eq.refl (app (rev v_Z) (app v_X v_Y)))))))))) (Eq.symm (Eq.refl (app (rev v_Z) (app v_X v_Y))))

-- Source held-out entry: rev_nested_other
theorem held_rev_nested_other (v_X : List α) (v_Y : List α) (v_Z : List α) : (rev (app v_X (rev (app v_Y v_Z)))) = (app (app v_Y v_Z) (rev v_X)) := by
  -- lemma_008, direction 1, AST path [1, 2]
  have left_000 : (rev (app v_X (rev (app v_Y v_Z)))) = (rev (app v_X (app (rev v_Z) (rev v_Y)))) := (congrArg (fun (replay_hole : List α) => (rev (app v_X replay_hole))) (lib_lemma_008 (α := α) (v_X := v_Y) (v_Y := v_Z)))
  -- lemma_008, direction 1, AST path []
  have left_001 : (rev (app v_X (app (rev v_Z) (rev v_Y)))) = (app (rev (app (rev v_Z) (rev v_Y))) (rev v_X)) := (lib_lemma_008 (α := α) (v_X := v_X) (v_Y := (app (rev v_Z) (rev v_Y))))
  -- lemma_008, direction 1, AST path [1]
  have left_002 : (app (rev (app (rev v_Z) (rev v_Y))) (rev v_X)) = (app (app (rev (rev v_Y)) (rev (rev v_Z))) (rev v_X)) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev v_X))) (lib_lemma_008 (α := α) (v_X := (rev v_Z)) (v_Y := (rev v_Y))))
  -- training_cached, direction 1, AST path [1, 1]
  have left_003 : (app (app (rev (rev v_Y)) (rev (rev v_Z))) (rev v_X)) = (app (app v_Y (rev (rev v_Z))) (rev v_X)) := (congrArg (fun (replay_hole : List α) => (app (app replay_hole (rev (rev v_Z))) (rev v_X))) (lib_training_cached (α := α) (v_X := v_Y)))
  -- training_cached, direction 1, AST path [1, 2]
  have left_004 : (app (app v_Y (rev (rev v_Z))) (rev v_X)) = (app (app v_Y v_Z) (rev v_X)) := (congrArg (fun (replay_hole : List α) => (app (app v_Y replay_hole) (rev v_X))) (lib_training_cached (α := α) (v_X := v_Z)))
  -- lemma_007, direction 1, AST path []
  have left_005 : (app (app v_Y v_Z) (rev v_X)) = (app v_Y (app v_Z (rev v_X))) := (lib_lemma_007 (α := α) (v_X := v_Y) (v_Y := v_Z) (v_Z := (rev v_X)))
  -- lemma_007, direction 1, AST path []
  have right_000 : (app (app v_Y v_Z) (rev v_X)) = (app v_Y (app v_Z (rev v_X))) := (lib_lemma_007 (α := α) (v_X := v_Y) (v_Y := v_Z) (v_Z := (rev v_X)))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.trans left_004 (Eq.trans left_005 (Eq.refl (app v_Y (app v_Z (rev v_X)))))))))) (Eq.symm (Eq.trans right_000 (Eq.refl (app v_Y (app v_Z (rev v_X))))))

-- Source held-out entry: rev_both
theorem held_rev_both (v_X : List α) (v_Y : List α) : (rev (app (rev v_X) (rev v_Y))) = (app v_Y v_X) := by
  -- lemma_008, direction 1, AST path []
  have left_000 : (rev (app (rev v_X) (rev v_Y))) = (app (rev (rev v_Y)) (rev (rev v_X))) := (lib_lemma_008 (α := α) (v_X := (rev v_X)) (v_Y := (rev v_Y)))
  -- training_cached, direction 1, AST path [1]
  have left_001 : (app (rev (rev v_Y)) (rev (rev v_X))) = (app v_Y (rev (rev v_X))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev (rev v_X)))) (lib_training_cached (α := α) (v_X := v_Y)))
  -- training_cached, direction 1, AST path [2]
  have left_002 : (app v_Y (rev (rev v_X))) = (app v_Y v_X) := (congrArg (fun (replay_hole : List α) => (app v_Y replay_hole)) (lib_training_cached (α := α) (v_X := v_X)))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.refl (app v_Y v_X))))) (Eq.symm (Eq.refl (app v_Y v_X)))

-- Source held-out entry: rev_double_pair
theorem held_rev_double_pair (v_X : List α) (v_Y : List α) : (rev (rev (app v_X v_Y))) = (app v_X v_Y) := by
  -- lemma_008, direction 1, AST path [1]
  have left_000 : (rev (rev (app v_X v_Y))) = (rev (app (rev v_Y) (rev v_X))) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (lib_lemma_008 (α := α) (v_X := v_X) (v_Y := v_Y)))
  -- lemma_008, direction 1, AST path []
  have left_001 : (rev (app (rev v_Y) (rev v_X))) = (app (rev (rev v_X)) (rev (rev v_Y))) := (lib_lemma_008 (α := α) (v_X := (rev v_Y)) (v_Y := (rev v_X)))
  -- training_cached, direction 1, AST path [1]
  have left_002 : (app (rev (rev v_X)) (rev (rev v_Y))) = (app v_X (rev (rev v_Y))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev (rev v_Y)))) (lib_training_cached (α := α) (v_X := v_X)))
  -- training_cached, direction 1, AST path [2]
  have left_003 : (app v_X (rev (rev v_Y))) = (app v_X v_Y) := (congrArg (fun (replay_hole : List α) => (app v_X replay_hole)) (lib_training_cached (α := α) (v_X := v_Y)))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.refl (app v_X v_Y)))))) (Eq.symm (Eq.refl (app v_X v_Y)))

-- Source held-out entry: rev_four_repeated
theorem held_rev_four_repeated (v_X : List α) (v_Y : List α) (v_Z : List α) : (rev (app (app v_X v_Y) (app v_Z v_X))) = (app (rev v_X) (app (rev v_Z) (app (rev v_Y) (rev v_X)))) := by
  -- lemma_007, direction 1, AST path [1]
  have left_000 : (rev (app (app v_X v_Y) (app v_Z v_X))) = (rev (app v_X (app v_Y (app v_Z v_X)))) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (lib_lemma_007 (α := α) (v_X := v_X) (v_Y := v_Y) (v_Z := (app v_Z v_X))))
  -- lemma_008, direction 1, AST path []
  have left_001 : (rev (app v_X (app v_Y (app v_Z v_X)))) = (app (rev (app v_Y (app v_Z v_X))) (rev v_X)) := (lib_lemma_008 (α := α) (v_X := v_X) (v_Y := (app v_Y (app v_Z v_X))))
  -- lemma_008, direction 1, AST path [1]
  have left_002 : (app (rev (app v_Y (app v_Z v_X))) (rev v_X)) = (app (app (rev (app v_Z v_X)) (rev v_Y)) (rev v_X)) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev v_X))) (lib_lemma_008 (α := α) (v_X := v_Y) (v_Y := (app v_Z v_X))))
  -- lemma_008, direction 1, AST path [1, 1]
  have left_003 : (app (app (rev (app v_Z v_X)) (rev v_Y)) (rev v_X)) = (app (app (app (rev v_X) (rev v_Z)) (rev v_Y)) (rev v_X)) := (congrArg (fun (replay_hole : List α) => (app (app replay_hole (rev v_Y)) (rev v_X))) (lib_lemma_008 (α := α) (v_X := v_Z) (v_Y := v_X)))
  -- lemma_007, direction 1, AST path [1]
  have left_004 : (app (app (app (rev v_X) (rev v_Z)) (rev v_Y)) (rev v_X)) = (app (app (rev v_X) (app (rev v_Z) (rev v_Y))) (rev v_X)) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev v_X))) (lib_lemma_007 (α := α) (v_X := (rev v_X)) (v_Y := (rev v_Z)) (v_Z := (rev v_Y))))
  -- lemma_007, direction 1, AST path []
  have left_005 : (app (app (rev v_X) (app (rev v_Z) (rev v_Y))) (rev v_X)) = (app (rev v_X) (app (app (rev v_Z) (rev v_Y)) (rev v_X))) := (lib_lemma_007 (α := α) (v_X := (rev v_X)) (v_Y := (app (rev v_Z) (rev v_Y))) (v_Z := (rev v_X)))
  -- lemma_007, direction 1, AST path [2]
  have left_006 : (app (rev v_X) (app (app (rev v_Z) (rev v_Y)) (rev v_X))) = (app (rev v_X) (app (rev v_Z) (app (rev v_Y) (rev v_X)))) := (congrArg (fun (replay_hole : List α) => (app (rev v_X) replay_hole)) (lib_lemma_007 (α := α) (v_X := (rev v_Z)) (v_Y := (rev v_Y)) (v_Z := (rev v_X))))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.trans left_004 (Eq.trans left_005 (Eq.trans left_006 (Eq.refl (app (rev v_X) (app (rev v_Z) (app (rev v_Y) (rev v_X)))))))))))) (Eq.symm (Eq.refl (app (rev v_X) (app (rev v_Z) (app (rev v_Y) (rev v_X))))))

-- Source held-out entry: rev_cons_append
theorem held_rev_cons_append (e_a : α) (v_X : List α) (v_Y : List α) : (rev (app (List.cons e_a v_X) v_Y)) = (app (rev v_Y) (app (rev v_X) (List.cons e_a ([] : List α)))) := by
  -- app_cons, direction 1, AST path [1]
  have left_000 : (rev (app (List.cons e_a v_X) v_Y)) = (rev (List.cons e_a (app v_X v_Y))) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (app_cons (α := α) (e_a := e_a) (v_X := v_X) (v_Y := v_Y)))
  -- rev_cons, direction 1, AST path []
  have left_001 : (rev (List.cons e_a (app v_X v_Y))) = (app (rev (app v_X v_Y)) (List.cons e_a ([] : List α))) := (rev_cons (α := α) (e_a := e_a) (v_X := (app v_X v_Y)))
  -- lemma_008, direction 1, AST path [1]
  have left_002 : (app (rev (app v_X v_Y)) (List.cons e_a ([] : List α))) = (app (app (rev v_Y) (rev v_X)) (List.cons e_a ([] : List α))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (List.cons e_a ([] : List α)))) (lib_lemma_008 (α := α) (v_X := v_X) (v_Y := v_Y)))
  -- lemma_007, direction 1, AST path []
  have left_003 : (app (app (rev v_Y) (rev v_X)) (List.cons e_a ([] : List α))) = (app (rev v_Y) (app (rev v_X) (List.cons e_a ([] : List α)))) := (lib_lemma_007 (α := α) (v_X := (rev v_Y)) (v_Y := (rev v_X)) (v_Z := (List.cons e_a ([] : List α))))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.refl (app (rev v_Y) (app (rev v_X) (List.cons e_a ([] : List α))))))))) (Eq.symm (Eq.refl (app (rev v_Y) (app (rev v_X) (List.cons e_a ([] : List α))))))

-- Source held-out entry: nested_involution
theorem held_nested_involution (v_X : List α) (v_Y : List α) (v_Z : List α) : (rev (app (rev (app (rev v_X) v_Y)) v_Z)) = (app (rev v_Z) (app (rev v_X) v_Y)) := by
  -- lemma_008, direction 1, AST path [1, 1]
  have left_000 : (rev (app (rev (app (rev v_X) v_Y)) v_Z)) = (rev (app (app (rev v_Y) (rev (rev v_X))) v_Z)) := (congrArg (fun (replay_hole : List α) => (rev (app replay_hole v_Z))) (lib_lemma_008 (α := α) (v_X := (rev v_X)) (v_Y := v_Y)))
  -- training_cached, direction 1, AST path [1, 1, 2]
  have left_001 : (rev (app (app (rev v_Y) (rev (rev v_X))) v_Z)) = (rev (app (app (rev v_Y) v_X) v_Z)) := (congrArg (fun (replay_hole : List α) => (rev (app (app (rev v_Y) replay_hole) v_Z))) (lib_training_cached (α := α) (v_X := v_X)))
  -- lemma_007, direction 1, AST path [1]
  have left_002 : (rev (app (app (rev v_Y) v_X) v_Z)) = (rev (app (rev v_Y) (app v_X v_Z))) := (congrArg (fun (replay_hole : List α) => (rev replay_hole)) (lib_lemma_007 (α := α) (v_X := (rev v_Y)) (v_Y := v_X) (v_Z := v_Z)))
  -- lemma_008, direction 1, AST path []
  have left_003 : (rev (app (rev v_Y) (app v_X v_Z))) = (app (rev (app v_X v_Z)) (rev (rev v_Y))) := (lib_lemma_008 (α := α) (v_X := (rev v_Y)) (v_Y := (app v_X v_Z)))
  -- lemma_008, direction 1, AST path [1]
  have left_004 : (app (rev (app v_X v_Z)) (rev (rev v_Y))) = (app (app (rev v_Z) (rev v_X)) (rev (rev v_Y))) := (congrArg (fun (replay_hole : List α) => (app replay_hole (rev (rev v_Y)))) (lib_lemma_008 (α := α) (v_X := v_X) (v_Y := v_Z)))
  -- training_cached, direction 1, AST path [2]
  have left_005 : (app (app (rev v_Z) (rev v_X)) (rev (rev v_Y))) = (app (app (rev v_Z) (rev v_X)) v_Y) := (congrArg (fun (replay_hole : List α) => (app (app (rev v_Z) (rev v_X)) replay_hole)) (lib_training_cached (α := α) (v_X := v_Y)))
  -- lemma_007, direction 1, AST path []
  have left_006 : (app (app (rev v_Z) (rev v_X)) v_Y) = (app (rev v_Z) (app (rev v_X) v_Y)) := (lib_lemma_007 (α := α) (v_X := (rev v_Z)) (v_Y := (rev v_X)) (v_Z := v_Y))
  exact Eq.trans (Eq.trans left_000 (Eq.trans left_001 (Eq.trans left_002 (Eq.trans left_003 (Eq.trans left_004 (Eq.trans left_005 (Eq.trans left_006 (Eq.refl (app (rev v_Z) (app (rev v_X) v_Y)))))))))) (Eq.symm (Eq.refl (app (rev v_Z) (app (rev v_X) v_Y))))

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
#print axioms lib_lemma_000
#print axioms lib_lemma_001
#print axioms lib_lemma_002
#print axioms lib_lemma_003
#print axioms lib_lemma_004
#print axioms lib_lemma_005
#print axioms lib_lemma_006
#print axioms lib_lemma_007
#print axioms lib_lemma_008
#print axioms lib_training_cached
#print axioms held_rev_app
#print axioms held_rev_revapp_left
#print axioms held_rev_revapp_right
#print axioms held_rev_three_left
#print axioms held_rev_three_right
#print axioms held_rev_nested
#print axioms held_rev_nested_other
#print axioms held_rev_both
#print axioms held_rev_double_pair
#print axioms held_rev_four_repeated
#print axioms held_rev_cons_append
#print axioms held_nested_involution
#print axioms held_app_nil_def
#print axioms held_app_cons_def
#print axioms held_app_two_cons_def
#print axioms held_app_nil_nested
#print axioms held_app_cons_nil_def
#print axioms held_rev_cons_nil_def
#print axioms held_rev_two_cons_def
#print axioms held_rev_nil_def
end CertificateReplay
