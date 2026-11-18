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
-- Concrete object computation for the actual multiplication; both tags disappear.
example : (flat.obj (laid.obj x)).1 = 3 := rfl
example : grade _ _ (flat.obj (laid.obj x)).2 = (1:Nat) := rfl
example : grade _ _ (payload _ _ (flat.obj (laid.obj x)).2) = (2:Nat) := rfl
example : grade _ _ (payload _ _ (payload _ _ (flat.obj (laid.obj x)).2)) = (1:Nat) := rfl
-- Project the full functor equation to this particular nonidentity arrow.
-- Keeping the target equality transport explicit avoids reducing a transported
-- dependent arrow merely to express its type.
theorem mapWitness {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (h : F = G) {x y : C} (f : x ⟶ y) : TelescopeSquares.Aligned (F.map f) (G.map f) := by
  subst G; exact TelescopeSquares.Aligned.refl _
theorem mapAt {X Z : Natᵒᵖ ⥤ Cat.{0,0}} {F G : X ⟶ Z}
    (h : F = G) (A : Natᵒᵖ) {x y : X.obj A} (f : x ⟶ y) :
    TelescopeSquares.Aligned ((F.app A).toFunctor.map f) ((G.app A).toFunctor.map f) :=
  mapWitness (congrArg Cat.Hom.toFunctor (NatTrans.congr_app h A)) f
#check mapAt (PackedFree.join_summand S Y 2 1) (op 2) (x := x) (y := y) arr
example : (payloadMap (payloadMap (payloadMap arr))) (⟨4,by decide⟩ : Fin 6) = [4,9] := rfl
example : ¬ IsIso arr := by
  intro h
  obtain ⟨g,_,_⟩ := h.out
  have k := gradeMap g
  exact (by decide : ¬ 3 ≤ 1) (leOfHom (show (3:Nat) ⟶ 1 from k))
-- Finite coordinates really restrict along a noninvertible base inclusion.
def pointWord : (fun _ : Fin 6 => Letter.pt) ⟶ (fun _ : Fin 6 => Letter.pt) := fun i => [i.val,9]
example : ((Y.map (show (5:Nat) ⟶ 6 from homOfLE (by decide)).op).toFunctor.map pointWord) ⟨3,by decide⟩ = [3,9] := rfl
example : ((((PackedFree.monad S).η.app Y).app (op 2)).toFunctor.obj (fun _ => Letter.pt)).1 = 0 := rfl
example : ((((PackedFree.generator S).app Y).app (op 2)).toFunctor.obj (pair _ _ (1 : Nat) (fun _ => Letter.pt))).1 = 1 := rfl
end Moving
