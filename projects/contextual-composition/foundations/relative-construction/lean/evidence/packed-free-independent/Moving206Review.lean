import ContextualComposition.PackedFree
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep
namespace Moving
set_option maxHeartbeats 400000
-- Native grades and their nonidentity arrows genuinely change the extended context.
def extend (a : Nat) : Nat ⥤ Nat where
  obj k := a+k
  map h := homOfLE (Nat.add_le_add_left h.le a)
  map_id _ := rfl
  map_comp _ _ := rfl
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Nat)
  extend := extend
  lift {a d} f := { app := fun k => homOfLE (Nat.add_le_add_right f.le k) }
theorem S : P.Split where
  lift_id _ := HEq.rfl
  lift_comp _ _ := HEq.rfl
-- A nonthin terminal payload category: arrow labels retain an ordered word.
inductive Letter | pt
instance : Category Letter where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp := by intro; intros; apply List.nil_append
  comp_id := by intro; intros; apply List.append_nil
  assoc := by intro; intros; apply List.append_assoc
def Y : Natᵒᵖ ⥤ Cat.{0,0} where
  obj a := Cat.of (Fin a.unop → Letter)
  map {a _} f := (Pi.comap (fun _ : Fin a.unop => Letter) (Fin.castLE f.unop.le)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
abbrev L (n : Nat) := PackedFree.pow S Y n
def tail (k l : Nat) : (L 2).obj (op k) := pair _ _ l (pair _ _ (1 : Nat) (fun _ => Letter.pt))
def nested (a k l : Nat) : (PackedFree.pow S (L 2) 1).obj (op a) := pair _ _ k (tail (a+k) l)
abbrev x := nested 2 1 2
abbrev y := nested 2 3 4
-- The three arrows of grades are 1→3, 2→4, 1→1. The endpoint of x is 6;
-- at that endpoint, the terminal payload map retains the coordinate itself.
def arr : x ⟶ y :=
  arrow (x := x) (y := y) (show (1:Nat) ⟶ 3 from homOfLE (by decide))
    (arrow (x := payload _ _ x) (y := _) (show (2:Nat) ⟶ 4 from homOfLE (by decide))
      (arrow (x := payload _ _ (payload _ _ x)) (y := _) (𝟙 _)
        (fun i => [i.val,9])))
def laid := ((ChainPayload.layerMap (PackedFree.inc S Y 2) S 1 ≫
  PackedFree.inc S ((PackedFree.free S).obj Y) 1).app (op 2)).toFunctor
def flat := ((PackedFree.join S Y).app (op 2)).toFunctor

set_option maxHeartbeats 500000 in
theorem flatOnArrow : flat.map (laid.map arr) = (Sigma.incl (C := fun n => (L n).obj (op 2)) 3).map arr := by
  let ee := congrArg Cat.Hom.toFunctor (NatTrans.congr_app (PackedFree.join_summand S Y 2 1) (op 2))
  exact (Functor.congr_hom ee arr).trans (by
    change 𝟙 _ ≫ (Sigma.incl (C := fun n => (L n).obj (op 2)) 3).map arr ≫ 𝟙 _ = _
    simp)

abbrev incl3 := Sigma.incl (C := fun n => (L n).obj (op 2)) 3
noncomputable def recovered : x ⟶ y := incl3.preimage (flat.map (laid.map arr))
theorem recovered_eq : recovered = arr := by
  apply incl3.map_injective
  change incl3.map (incl3.preimage _) = _
  exact (incl3.map_preimage (X := x) (Y := y) (flat.map (laid.map arr))).trans flatOnArrow
example : (payloadMap (payloadMap (payloadMap recovered))) (⟨4,by decide⟩ : Fin 6) = [4,9] := by
  rw [recovered_eq]; rfl
def arr2 : y ⟶ nested 2 5 7 :=
  arrow (x := y) (y := _) (show (3:Nat) ⟶ 5 from homOfLE (by decide))
    (arrow (x := payload _ _ y) (y := _) (show (4:Nat) ⟶ 7 from homOfLE (by decide))
      (arrow (x := payload _ _ (payload _ _ y)) (y := _) (𝟙 _) (fun i => [10+i.val])))
theorem flatOnComposed : flat.map (laid.map (arr ≫ arr2)) = incl3.map (arr ≫ arr2) := by
  let ee := congrArg Cat.Hom.toFunctor (NatTrans.congr_app (PackedFree.join_summand S Y 2 1) (op 2))
  exact (Functor.congr_hom ee (arr ≫ arr2)).trans (by
    change 𝟙 _ ≫ incl3.map (arr ≫ arr2) ≫ 𝟙 _ = _; simp)
example : (payloadMap (payloadMap (payloadMap (arr ≫ arr2)))) (⟨4,by decide⟩ : Fin 6) = [4,9,14] := rfl
def xyz := (flat.obj (laid.obj (nested 2 5 7))).2
example : (grade _ _ xyz, grade _ _ (payload _ _ xyz), grade _ _ (payload _ _ (payload _ _ xyz))) =
    ((5:Nat),(7:Nat),(1:Nat)) := rfl
end Moving
