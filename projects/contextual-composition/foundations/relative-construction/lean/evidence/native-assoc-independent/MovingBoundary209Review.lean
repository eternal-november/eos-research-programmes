import ContextualComposition.NativeTriple
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativeAssoc
namespace MovingBoundary209
set_option backward.isDefEq.respectTransparency false
inductive B | star
instance : Category B where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
abbrev b := B.star
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of (Discrete Unit))
  extend _ := (Functor.const _).obj b
  lift f := { app := fun _ => f, naturality := by intros; rfl }
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def a : tel S := ⟨1,pair P.grades (𝟭 B) b (Discrete.mk ())⟩
def e : tel S := ⟨0,b⟩
def aMap (f : b ⟶ b) : a ⟶ a := (incl S 1).map (arrow (x := a.2) (y := a.2) f (𝟙 _))
def eMap (f : b ⟶ b) : e ⟶ e := (incl S 0).map f
def row : (word S 2).apex := ⟨a,e,rfl⟩
def onRow (f : b ⟶ b) : row ⟶ row := ⟨⟨aMap f,eMap f,rfl⟩⟩
def rowA : strings S := ⟨2,row⟩
def rowB : strings S := ⟨1,a⟩
def x : Three.strings3 S := ⟨2,⟨rowA,rowB,rfl⟩⟩
def onX (f : b ⟶ b) : x ⟶ x :=
  (Three.incl3 S 2).map ⟨⟨(outer S 2).map (onRow f),(outer S 1).map (aMap f),rfl⟩⟩
def yes : b ⟶ b := fun _ => true
def no : b ⟶ b := fun _ => false
-- The matching equation is not given by parallelism of the component arrows.
example (h : row ⟶ row) (l : h.hom.fst = aMap yes) (r : h.hom.snd = eMap no) : False := by
  have w := h.hom.w
  rw [l,r] at w
  exact Bool.noConfusion (congrFun w false)
example : onX yes ≫ onX no ≠ onX no ≫ onX yes := by
  intro h
  have k := congrArg (Three.dest S).map h
  exact Bool.noConfusion (congrFun k false)
def Y : Bᵒᵖ ⥤ Cat.{0,0} where
  obj _ := Cat.of (Bool → Nat)
  map f := (Pi.comap (fun _ : Bool => Nat) (show Bool → Bool from f.unop)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
def p := pair Y (Three.dest S) x (fun _ => 1)
def q := pair Y (Three.dest S) x (fun b => if b then 1 else 0)
def good : p ⟶ q := arrow (onX yes) (fun _ => homOfLE (le_refl (1:Nat)))
theorem noFalse : ¬ ∃ t : p ⟶ q, gradeMap t = onX no := by
  rintro ⟨t, ht⟩
  have h := payloadMap t
  rw [ht] at h
  exact (by decide : ¬ 1 ≤ 0) (leOfHom (h false))
noncomputable abbrev M := Three.weightedOuter S Y ⋙ BlockCartesian.All.weighted S Y
noncomputable abbrev I := Three.weightedInner S Y ⋙ BlockCartesian.All.weighted S Y
example : TelescopeSquares.Aligned (M.map good) (I.map good) := NativeCube.functorAlign (Three.weighted_assoc S Y) good
-- On the flattened weighted maps the terminal-context action is still the nonidentity constant-true map.
noncomputable abbrev destM := M ⋙ gradeProjection ⋙ rightLeg S
theorem endpoint : destM = gradeProjection (Y := Y) (e := Three.dest S) ⋙ Three.dest S := by
  let X := Three.weightedOuter S Y
  let W := BlockCartesian.All.weighted S Y
  calc
    _ = X ⋙ (gradeProjection ⋙ flatten S) ⋙ rightLeg S := congrArg (fun f => X ⋙ f ⋙ rightLeg S)
      (SpanPayload.total_projection Y (flatten S) (rightLeg S) (flatten_dest S))
    _ = (X ⋙ gradeProjection) ⋙ Rows.dest S := congrArg (fun f => (X ⋙ gradeProjection) ⋙ f) (flatten_dest S)
    _ = gradeProjection ⋙ Three.mergeRows S ⋙ Rows.dest S := congrArg (· ⋙ Rows.dest S)
      (SpanPayload.total_projection Y (Three.mergeRows S) (Rows.dest S) (Three.merge_dest S))
    _ = _ := congrArg (gradeProjection ⋙ ·) (Three.merge_dest S)
theorem labels {x y x' y' : B} {f : x ⟶ y} {g : x' ⟶ y'} (h : TelescopeSquares.Aligned f g) :
    (show Bool → Bool from f) = (show Bool → Bool from g) := by
  obtain ⟨hx,hy,h⟩ := h; subst x'; subst y'; simpa using h
example : (show Bool → Bool from destM.map good) false = true := by
  have h := labels (NativeCube.functorAlign endpoint good)
  exact congrFun h false
end MovingBoundary209
