import ContextualComposition.EndpointInterpretation
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep PackedFree
namespace MovingInterpretationProbe
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
def e (d A : Nat) : Nat ⥤ Nat where
  obj k := A + d*k
  map h := homOfLE (Nat.add_le_add_left (Nat.mul_le_mul_left d h.le) A)
  map_id _ := rfl
  map_comp _ _ := rfl
def P (d : Nat) : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Nat)
  extend := e d
  lift {A D} f := {app := fun k => homOfLE (Nat.add_le_add_right f.le _)}
theorem S (d) : (P d).Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def lower : EndpointInterpretation.Map (P 2) (P 1) where
  grade _ := 𝟭 _
  endpoint A := {app := fun k => homOfLE (Nat.add_le_add_left (Nat.mul_le_mul_right k (by decide : 1 ≤ 2)) A)}
  grade_square _ := rfl
  endpoint_square _ := by apply heq_of_eq; apply Subsingleton.elim
inductive Letter | pt
instance : Category Letter where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp _ := List.nil_append _
  comp_id _ := List.append_nil _
  assoc _ _ _ := List.append_assoc _ _ _
def Y : Natᵒᵖ ⥤ Cat.{0,0} where
  obj a := Cat.of (Fin a.unop → Letter)
  map {a _} f := (Pi.comap (fun _ : Fin a.unop => Letter) (Fin.castLE f.unop.le)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
def x (k : Nat) : Total Y ((P 2).extend 3) := pair Y _ k (fun _ => Letter.pt)
def f (w : Fin 7 → List Nat) : x 2 ⟶ x 4 := arrow (show (2:Nat) ⟶ 4 from homOfLE (by decide)) w
def forward (i : Fin 7) := [i.val,9]
def reverse (i : Fin 7) := [9,i.val]
def hidden (i : Fin 7) := if i.val=6 then [123] else forward i
abbrev H := EndpointInterpretation.fibre lower Y 3
example : ¬ IsIso ((lower.endpoint 3).app (2:Nat)) := by
  intro h
  exact (by decide : ¬7 ≤ 5) (leOfHom (inv ((lower.endpoint 3).app (2:Nat))))
example : gradeMap (H.map (f forward)) = (show (2:Nat) ⟶ 4 from homOfLE (by decide)) := rfl
theorem witness (w : Fin 7 → List Nat) (i : Fin 5) : payloadMap (H.map (f w)) i = w ⟨i.val,by omega⟩ := by
  change w _ ++ [] = _
  exact List.append_nil _
theorem separated : H.map (f forward) ≠ H.map (f reverse) := by
  intro j
  have d := congrArg (fun t : H.obj (x 2) ⟶ H.obj (x 4) => payloadMap t (⟨3,by decide⟩ : Fin 5)) j
  rw [witness,witness] at d
  exact (by decide : [3,9] ≠ [9,3]) d
theorem erased : H.map (f hidden) = H.map (f forward) := by
  apply (homEquiv _ _).injective; apply Sigma.ext (by rfl); apply heq_of_eq; funext i
  change payloadMap (H.map (f hidden)) (i : Fin 5) = payloadMap (H.map (f forward)) (i : Fin 5)
  have hi : i.val < 5 := i.isLt
  rw [witness,witness]; simp [hidden,show i.val ≠ 6 by omega]
theorem inputDiff : f hidden ≠ f forward := by
  intro e
  have j := congrArg (fun t : x 2 ⟶ x 4 => payloadMap t (⟨6,by decide⟩ : Fin 7)) e
  exact (by decide : [123] ≠ [6,9]) j
abbrev I (d : Nat) := ((inc (S d) Y 1).app (op 3)).toFunctor
abbrev F := (((EndpointInterpretation.packed lower (S 2) (S 1)).app Y).app (op 3)).toFunctor
example : (I 2 ⋙ F).map (f forward) ≠ (I 2 ⋙ F).map (f reverse) := by
  rw [EndpointInterpretation.oneLayer lower (S 2) (S 1) Y 3]
  exact fun h => separated ((Sigma.incl (C := fun n => ((pow (S 1) Y n).obj (op 3) : Type)) 1).map_injective h)
example : (I 2 ⋙ F).map (f hidden) = (I 2 ⋙ F).map (f forward) := by
  rw [EndpointInterpretation.oneLayer lower (S 2) (S 1) Y 3]
  exact congrArg (I 1).map erased
end MovingInterpretationProbe
