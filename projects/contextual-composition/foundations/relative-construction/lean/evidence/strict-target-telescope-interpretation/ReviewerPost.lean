import Lean.Util.FoldConsts
import ContextualComposition.EndpointInterpretation
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep PackedFree TelescopeInterpretation
namespace ReviewerPost
set_option backward.isDefEq.respectTransparency false
abbrev B := Discrete Unit
abbrev b : B := ⟨()⟩
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of (Discrete Bool))
  extend _ := (Functor.const _).obj b
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => by apply heq_of_eq; apply Subsingleton.elim⟩
def changeLetters (g : Bool → Bool) : EndpointInterpretation.Map P P where
  grade _ := Discrete.functor (fun z => Discrete.mk (g z))
  endpoint _ := 𝟙 _
  grade_square _ := rfl
  endpoint_square _ := by apply heq_of_eq; apply Subsingleton.elim
abbrev change (g : Bool → Bool) := EndpointInterpretation.packed (changeLetters g) S S
abbrev T := monad S
abbrev erase := change (fun _ => false)
abbrev flip := change Bool.not
abbrev q := EndpointInterpretation.oneStep (changeLetters (fun _ => false)) S S ≫ generator S
example : erase ≫ flip = extend S T (q ≫ flip.toNatTrans) := extend_post S T q flip
abbrev Z : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of B)
-- Three independently chosen grade letters followed by a payload.
def word : (pow S Z 3).obj (op b) := pair _ _ (Discrete.mk true) (pair _ _ (Discrete.mk false) (pair _ _ (Discrete.mk true) b))
abbrev item := ((inc S Z 3).app (op b)).toFunctor.obj word
def read3 : (free S |>.obj Z |>.obj (op b)) → Option (Bool × Bool × Bool)
  | ⟨3,x⟩ => some ((grade _ _ x).as,(grade _ _ (payload _ _ x)).as,(grade _ _ (payload _ _ (payload _ _ x))).as)
  | _ => none
def observed (f : T ⟶ T) := read3 (((f.app Z).app (op b)).toFunctor.obj item)
example : observed (𝟙 T) = some (true,false,true) := rfl
example : observed flip = some (false,true,false) := rfl
example : observed (erase ≫ flip) = some (true,true,true) := rfl
example : observed (flip ≫ erase) = some (false,false,false) := rfl
example : erase ≫ flip ≠ flip ≫ erase := by
  intro h
  have hh := congrArg observed h
  exact (by decide : some (true,true,true) ≠ some (false,false,false)) hh

-- Actual three-layer arrows: this positive row test does not reduce to object grades.
inductive Letter | pt
instance : Category Letter where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp _ := List.nil_append _
  comp_id _ := List.append_nil _
  assoc _ _ _ := List.append_assoc _ _ _
abbrev Y : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of Letter)
abbrev y1 : (pow S Y 1).obj (op b) := pair _ _ (Discrete.mk true) Letter.pt
abbrev y2 : (pow S Y 2).obj (op b) := pair _ _ (Discrete.mk false) y1
abbrev y3 : (pow S Y 3).obj (op b) := pair _ _ (Discrete.mk true) y2
def a1 (w : List Nat) : y1 ⟶ y1 := arrow (𝟙 _) w
def a2 (w : List Nat) : y2 ⟶ y2 := arrow (𝟙 _) (a1 w)
def a3 (w : List Nat) : y3 ⟶ y3 := arrow (𝟙 _) (a2 w)
abbrev I := ((inc S Y 3).app (op b)).toFunctor
abbrev F := ((flip.app Y).app (op b)).toFunctor
abbrev W := ((EndpointInterpretation.layer (changeLetters Bool.not) S S Y 3).app (op b)).toFunctor
def readArrow {v w : (pow S Y 3).obj (op b)} (h : v ⟶ w) : List Nat := payloadMap (payloadMap (payloadMap h))
theorem threeRow : I ⋙ F = W ⋙ I :=
  congrArg Cat.Hom.toFunctor (NatTrans.congr_app (EndpointInterpretation.row (changeLetters Bool.not) S S Y 3) (op b))
example : readArrow (W.map (a3 [1,2])) = [1,2] := rfl
example : (I ⋙ F).map (a3 [1,2]) ≠ (I ⋙ F).map (a3 [2,1]) := by
  rw [threeRow]
  intro h
  have eq := (Sigma.incl (C := fun n => ((pow S Y n).obj (op b) : Type)) 3).map_injective h
  exact (by decide : [1,2] ≠ [2,1]) (congrArg readArrow eq)
end ReviewerPost

open Lean Elab Command
private partial def readDeps (env : Environment) (todo : List Name) (seen : NameSet) : NameSet := Id.run do
  match todo with
  | [] => return seen
  | n :: ns =>
    if seen.contains n || !(`ContextualComposition).isPrefixOf n then return readDeps env ns seen
    let next := seen.insert n
    match env.find? n with
    | none => return readDeps env ns next
    | some c => return readDeps env (c.getUsedConstantsAsSet.toList ++ ns) next
run_cmd do
  let env ← getEnv
  let d := readDeps env [``EndpointInterpretation.layer] {}
  for bad in [``EndpointInterpretation.packed,``EndpointInterpretation.row,``TelescopeInterpretation.interpret,``TelescopeInterpretation.universal,``PackedFree.fold] do
    if d.contains bad then throwError "Nominally independent fixed-layer algorithm uses {bad}"
  for good in [``EndpointInterpretation.oneStep,``EndpointInterpretation.fibre,``ContextualComposition.GrothendieckStep.restrict] do
    unless d.contains good do throwError "Expected native dependency {good} not found"
