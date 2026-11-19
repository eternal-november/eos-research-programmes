import ContextualComposition.ContextadTensorLift
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep PackedFree TelescopeSquares SpanPayload.Power
namespace NativeActionProbe
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
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
def cut (n : Nat) : Nat ⥤ Nat where
  obj k := min k n
  map f := homOfLE (by have h := f.le; omega)
  map_id _ := rfl
  map_comp _ _ := rfl
def counit (n : Nat) : cut n ⟶ 𝟭 Nat where
  app k := homOfLE (min_le_left k n)
def U : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Nat)
  extend A := (Functor.const Nat).obj (min A 2)
  lift f := {app := fun _ => (cut 2).map f}
theorem US : U.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def un : ContextadUnit.Data U where
  grade _ := (7 : Nat)
  discharge A := (counit 2).app A
  reindex _ := rfl
  square _ := Subsingleton.elim _ _
abbrev H := (((ContextadUnit.unit un US).app Y).app (op 5)).toFunctor
def x (n : Nat) : Y.obj (op n) := fun _ => Letter.pt
def forward (i : Fin 5) := [i.val,9]
def reverse (i : Fin 5) := [9,i.val]
def hidden (i : Fin 5) := if i.val=4 then [123] else forward i
theorem unitProbe (w : Fin 5 → List Nat) (i : Fin 2) :
    payloadMap (H.map (X := x 5) (Y := x 5) w) i = w ⟨i.val,by omega⟩ := by
  change w _ ++ [] = _
  exact List.append_nil _
example : ¬ IsIso (un.discharge 5) := by intro h; exact (by decide : ¬5 ≤ 2) (leOfHom (inv (un.discharge 5)))
theorem separated : H.map (X := x 5) (Y := x 5) forward ≠ H.map reverse := by
  intro e
  have h := congrArg (fun t : H.obj (x 5) ⟶ H.obj (x 5) => payloadMap t (⟨1,by decide⟩ : Fin 2)) e
  rw [unitProbe,unitProbe] at h
  exact (by decide : [1,9] ≠ [9,1]) h
theorem erased : H.map (X := x 5) (Y := x 5) hidden = H.map forward := by
  apply (homEquiv _ _).injective; apply Sigma.ext (by rfl); apply heq_of_eq; funext i
  change payloadMap (H.map (X := x 5) (Y := x 5) hidden) (i : Fin 2) = payloadMap (H.map forward) i
  rw [unitProbe,unitProbe]; simp [hidden,show i.val ≠ 4 by have hi : i.val < 2 := i.isLt; omega]
example : hidden ≠ forward := by intro e; exact (by decide : [123] ≠ [4,9]) (congrFun e ⟨4,by decide⟩)
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Nat)
  extend _ := 𝟭 Nat
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def data : ContextadTensor.Data S where
  tensor A := chainsEndpoint S 1 A ⋙ cut A
  delta A := whiskerLeft (chainsEndpoint S 1 A) (counit A)
def row (A p r : Nat) : Fibre.asCat (Y := Y) S 2 A := ⟨.cons p (.cons r (.nil _)),x r⟩
def moving (w : Fin 5 → List Nat) : row 3 1 5 ⟶ row 3 4 7 :=
  ⟨⟨(show (1:Nat) ⟶ 4 from homOfLE (by decide)),(show (5:Nat) ⟶ 7 from homOfLE (by decide)),PUnit.unit⟩,w⟩
abbrev R := ContextadTensor.rows data Y 3
example : gradeMap (R.map (moving forward)) = (show (3:Nat) ⟶ 3 from 𝟙 _) := rfl
theorem binaryProbe (w : Fin 5 → List Nat) (i : Fin 3) :
    payloadMap (R.map (moving w)) i = w ⟨i.val,by omega⟩ := by
  change w _ ++ [] = _
  exact List.append_nil _
theorem binarySeparated : R.map (moving forward) ≠ R.map (moving reverse) := by
  intro e
  have h := congrArg (fun t : R.obj (row 3 1 5) ⟶ R.obj (row 3 4 7) => payloadMap t (⟨2,by decide⟩ : Fin 3)) e
  rw [binaryProbe,binaryProbe] at h
  exact (by decide : [2,9] ≠ [9,2]) h
example : (Fibre.comparison S 2 3 ⋙ ContextadTensor.binary data Y 3).map (moving forward) ≠
    (Fibre.comparison S 2 3 ⋙ ContextadTensor.binary data Y 3).map (moving reverse) := by
  rw [ContextadTensor.read]; exact binarySeparated
def changing : row 3 0 1 ⟶ row 3 2 2 :=
  ⟨⟨(show (0:Nat) ⟶ 2 from homOfLE (by decide)),(show (1:Nat) ⟶ 2 from homOfLE (by decide)),PUnit.unit⟩,fun _ => [8,1]⟩
example : gradeMap (R.map changing) = (show (1:Nat) ⟶ 2 from homOfLE (by decide)) := rfl
example : ¬ IsIso (gradeMap (R.map changing)) := by
  intro h; exact (by decide : ¬2 ≤ 1) (leOfHom (inv (gradeMap (R.map changing))))
/-- Fibrewise tensor and natural delta do not imply even object-level exterior base change. -/
example : ¬ (((Iterates.layer P S Y 2).map (homOfLE (by decide : 2 ≤ 4)).op).toFunctor ⋙ ContextadTensor.binary data Y 2 =
    ContextadTensor.binary data Y 4 ⋙ P.baseRestrict Y (homOfLE (by decide : 2 ≤ 4))) := by
  intro e
  have q := (ContextadTensor.baseChange_iff data Y _).mp e
  have h := congrArg (grade Y (P.extend 2)) (Functor.congr_obj q (row 4 1 5))
  exact (by decide : (2:Nat) ≠ 4) h
def stable : ContextadTensor.Data S where
  tensor A := chainsEndpoint S 1 A ⋙ cut 3
  delta A := whiskerLeft (chainsEndpoint S 1 A) (counit 3)
theorem stableLift : ContextadTensorLift.Data stable where
  grade a t := by
    cases t with | cons p tail => cases tail with | cons r tail => cases tail; rfl
  square _ _ := Subsingleton.elim _ _
example : ¬ ContextadTensorLift.Data data := by
  intro h
  have bad := h.grade (show (2:Nat) ⟶ 4 from homOfLE (by decide : 2 ≤ 4)) (row 4 1 5).chain
  exact (by decide : (4:Nat) ≠ 2) bad
example (z : (Iterates.layer P S Y 2).obj (op 4)) :
    (ContextadTensor.binary stable Y 2).obj
      (((Iterates.layer P S Y 2).map (homOfLE (by decide : 2 ≤ 4)).op).toFunctor.obj z) =
    (P.baseRestrict Y (homOfLE (by decide : 2 ≤ 4))).obj ((ContextadTensor.binary stable Y 4).obj z) :=
  ContextadTensorLift.objects stable stableLift Y _ z
end NativeActionProbe
