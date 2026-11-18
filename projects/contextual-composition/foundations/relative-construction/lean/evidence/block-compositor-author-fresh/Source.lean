import ContextualComposition.BlockCompositor
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep
namespace Source212
set_option maxHeartbeats 1000000
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
open NativeBlocks NativeBlocks.Nested NativePacked NativeCleavage
def one (a k : Nat) : tel S := ⟨1,pair P.grades (𝟭 Nat) a k⟩
def obj (g h : Nat) : (pairSpan S).apex := ⟨one 3 g,one (3+g) h,rfl⟩
def z (g h : Nat) : (pairSpan S).source.Fiber 3 := ⟨obj g h,rfl⟩
def w (g h : Nat) : Lift.value Y 3 (pairSpan S) := pair Y _ (z g h) (fun _ => Letter.pt)
def a1 : one 3 1 ⟶ one 3 3 := (incl S 1).map (arrow (𝟙 (3:Nat)) (show (1:Nat) ⟶ 3 from homOfLE (by decide)))
def a2 : one 4 2 ⟶ one 6 4 := (incl S 1).map (arrow (show (4:Nat) ⟶ 6 from homOfLE (by decide)) (show (2:Nat) ⟶ 4 from homOfLE (by decide)))
def matching : obj 1 2 ⟶ obj 3 4 := ⟨⟨a1,a2,Subsingleton.elim _ _⟩⟩
def fixedSource : z 1 2 ⟶ z 3 4 := ⟨matching,IsHomLift.of_fac' _ _ _ rfl rfl (Subsingleton.elim _ _)⟩
def f : w 1 2 ⟶ w 3 4 := arrow fixedSource (fun i => [i.val,9])
def g : w 1 2 ⟶ w 3 4 := arrow fixedSource (fun i => [9,i.val])
example : (pairSpan S).dest.obj (obj 1 2) = 6 := rfl
example : (pairSpan S).dest.obj (obj 3 4) = 10 := rfl
theorem diff : f ≠ g := by
  intro e
  have h := congrArg (fun t : w 1 2 ⟶ w 3 4 => payloadMap t (⟨4,by decide⟩ : Fin 6)) e
  exact (by decide : [4,9] ≠ [9,4]) h
example : ¬ IsIso f := by
  intro hf; let := hf
  have h := (pairSpan S).dest.map (gradeMap (inv f)).1
  exact (by decide : ¬ 10 ≤ 6) (leOfHom h)

open BlockEvaluation CutCompositor CategoryTheory.Functor
noncomputable abbrev stage := stages S Y 3
noncomputable abbrev old := previous S Y 3
noncomputable abbrev v := BlockCompositor.compositor S Y 3
noncomputable abbrev nativeSquare := BlockCompositor.multiplicationSquare S Y 3
example : stage.map f ≫ v.hom.app (w 3 4) = v.hom.app (w 1 2) ≫ old.map f := v.hom.naturality f
example : stage.map f ≫ v.hom.app _ ≠ stage.map g ≫ v.hom.app _ := by
  intro h
  have k := (cancel_mono (v.hom.app (w 3 4))).mp h
  exact diff (stage.map_injective k)
example : (stage ⋙ multiplication S Y 3).map g ≫ nativeSquare.hom.app (w 3 4) =
    nativeSquare.hom.app (w 1 2) ≫ (native S Y 3).map g := nativeSquare.hom.naturality g
example : (compositorOfSquare S Y 3 nativeSquare).hom = v.hom := BlockCompositor.recovered S Y 3
end Source212
