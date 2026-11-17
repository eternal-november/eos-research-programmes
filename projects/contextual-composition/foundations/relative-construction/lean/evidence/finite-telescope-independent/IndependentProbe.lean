import ContextualComposition.FiniteTelescope
open ContextualComposition.FiniteTelescope
-- Here the choice of head changes the next vertex, unlike the shipped example.
private def br := fromExtension (fun _ : Nat => Bool) (fun a g => if g then a+2 else a+1)
private def p : Chain br 0 3 := .cons (b := 2) ⟨true,rfl⟩ (.cons (b := 3) ⟨false,rfl⟩ (.nil 3))
example : length p = 2 := rfl
example : IsEmpty {h : br 0 1 // h.val = true} := by
  constructor
  rintro ⟨⟨g,h⟩,rfl⟩
  contradiction
example : (1 : Fin 1).val = 0 := rfl
example : ¬ ∃ g : Fin 1, g.val = 1 := by decide
