import Mathlib.CategoryTheory.Products.Basic
import ContextualComposition.ContextadTensorLift
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep TelescopeSquares SpanPayload.Power
namespace MovingBaseProbe
open scoped CategoryTheory.Prod
noncomputable section
set_option backward.isDefEq.respectTransparency false
inductive W | pt
instance : Category W where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp _ := List.nil_append _
  comp_id _ := List.append_nil _
  assoc _ _ _ := List.append_assoc _ _ _
def twist (n : Nat) : Nat ⥤ Nat × W where
  obj k := (k,W.pt)
  map {a b} f := f ×ₘ (List.replicate (b-a) n : W.pt ⟶ W.pt)
  map_id k := by
    apply Prod.ext
    · rfl
    · change List.replicate (k-k) n = []; simp
  map_comp {a b c} f g := by
    apply Prod.ext
    · rfl
    · change List.replicate (c-a) n = List.replicate (b-a) n ++ List.replicate (c-b) n
      rw [List.replicate_append_replicate]; congr 1; have := f.le; have := g.le; omega
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of (Nat × W))
  extend _ := CategoryTheory.Prod.fst Nat W
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def data : ContextadTensor.Data S where
  tensor A := chainsEndpoint S 1 A ⋙ twist A
  delta A := {app := fun _ => 𝟙 _}
theorem holds : ContextadTensorLift.Data data where
  grade a t := by
    cases t with | cons p tail => cases tail with | cons r tail => cases tail; rfl
  square _ _ := Subsingleton.elim _ _
def Y : Natᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of (Discrete Unit))
def row (A r : Nat) : Fibre.asCat (Y := Y) S 2 A :=
  ⟨.cons ((0,W.pt) : Nat × W) (.cons ((r,W.pt) : Nat × W) (.nil _)),Discrete.mk ()⟩
def moving : row 4 1 ⟶ row 4 2 :=
  ⟨⟨((𝟙 (0:Nat)) ×ₘ (𝟙 W.pt)),((show (1:Nat) ⟶ 2 from homOfLE (by decide)) ×ₘ (𝟙 W.pt)),PUnit.unit⟩,𝟙 _⟩
abbrev a : (2:Nat) ⟶ 4 := homOfLE (by decide)
abbrev L := Fibre.pullFunctor (Y := Y) (n := 2) S a ⋙ ContextadTensor.rows data Y 2
abbrev R := ContextadTensor.rows data Y 4 ⋙ P.baseRestrict Y a
abbrev observe := (gradeProjection (Y := Y) (e := P.extend 2)) ⋙ CategoryTheory.Prod.snd Nat W
example : (L ⋙ observe).map moving = [2] := rfl
example : (R ⋙ observe).map moving = [4] := rfl
/-- Even native lift coherence on all objects and their entire fixed-chain coordinates
does not force the grade-arrow part of base change. -/
theorem fails : ¬ (((Iterates.layer P S Y 2).map a.op).toFunctor ⋙ ContextadTensor.binary data Y 2 =
    ContextadTensor.binary data Y 4 ⋙ P.baseRestrict Y a) := by
  intro h
  have q := (ContextadTensor.baseChange_iff data Y a).mp h
  have k := Functor.congr_hom (congrArg (· ⋙ observe) q) moving
  change [2] = eqToHom _ ≫ (show W.pt ⟶ W.pt from [4]) ≫ eqToHom _ at k
  simp at k
end
end MovingBaseProbe
