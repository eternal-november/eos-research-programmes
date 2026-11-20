module
public import ContextualComposition.RepresentableAssociatorFoldCells
public import ContextualComposition.RepresentableFoldLeftUnit
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliGeneric
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open CategoryTheory.Bicategory.Strict RepresentableStrictFold RepresentableKleisliConstraints
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
theorem symCast {D : Type*} [Category D] {x y : D} (e : x = y) : (eqToIso e).symm = eqToIso e.symm := by cases e; rfl
section
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {V W X Y Z : C}
def cmp (f : V ⟶ F.obj W) (g : W ⟶ F.obj X) := (f ≫ F.map g) ≫ μ X
def cell {f f' : V ⟶ F.obj W} {g g' : W ⟶ F.obj X} (t : f ⟶ f') (k : g ⟶ g') :
    cmp F μ f g ⟶ cmp F μ f' g' := RepresentableKleisli.horizontal t (F.map₂ k) ▷ μ X
theorem first {f f' : V ⟶ F.obj W} (t : f ⟶ f') (g : W ⟶ F.obj X) :
    cell F μ t (𝟙 g) = (t ▷ F.map g) ▷ μ X := by
  unfold cell RepresentableKleisli.horizontal
  rw [F.map₂_id,whiskerLeft_id,Category.comp_id]
theorem second (f : V ⟶ F.obj W) {g g' : W ⟶ F.obj X} (t : g ⟶ g') :
    cell F μ (𝟙 f) t = (f ◁ F.map₂ t) ▷ μ X := by
  unfold cell RepresentableKleisli.horizontal
  rw [id_whiskerRight,Category.id_comp]
def expand (g : W ⟶ F.obj X) (h : X ⟶ F.obj Y) :=
  unfoldThree F g (F.map h) (μ Y)
theorem fold (g : W ⟶ F.obj X) (h : X ⟶ F.obj Y) :
    F.map (cmp F μ g h) = (F.map g ≫ F.map (F.map h)) ≫ F.map (μ Y) := by
  simp only [cmp,F.map_comp]
theorem frame (g : W ⟶ F.obj X) (h : X ⟶ F.obj Y) :
    expand F μ g h = eqToIso (fold F μ g h) := castThree F g (F.map h) (μ Y) (fold F μ g h)
def bend (f : V ⟶ F.obj W) (g : W ⟶ F.obj X) (h : X ⟶ F.obj Y) :
    cmp F μ (cmp F μ f g) h ≅ cmp F μ f (cmp F μ g h) :=
  moveTail (f ≫ F.map g) (μ Y) (D h).symm ≪≫
    whiskerLeftIso ((f ≫ F.map g) ≫ F.map (F.map h)) (a Y) ≪≫
    moveHead f (F.map g) (F.map (F.map h)) (F.map (μ Y)) (μ Y) ≪≫
    whiskerRightIso (whiskerLeftIso f (expand F μ g h).symm) (μ Y)
theorem shape (f : V ⟶ F.obj W) (g : W ⟶ F.obj X) (h : X ⟶ F.obj Y) :
    bend F μ D a f g h = RepresentableAssociatorPrefix.word f (F.map g) (μ X) (F.map h) (μ Y)
      (F.map (F.map h)) (μ (F.obj Y)) (F.map (μ Y)) (D h).symm (a Y) (F.map (cmp F μ g h)) (fold F μ g h).symm := by
  unfold bend RepresentableAssociatorPrefix.word
  rw [frame,symCast,castLeft,castRight]
theorem firstFold {f f' : V ⟶ F.obj W} (t : f ⟶ f') (g : W ⟶ F.obj X) :
    F.map₂ (cell F μ t (𝟙 g)) ≫ (expand F μ f' g).hom =
      (expand F μ f g).hom ≫ (F.map₂ t ▷ F.map (F.map g)) ▷ F.map (μ X) := by
  rw [first]
  exact RepresentableAssociatorFoldCells.first F (μ X) (p := F.map g) t
theorem secondFold (f : V ⟶ F.obj W) {g g' : W ⟶ F.obj X} (t : g ⟶ g') :
    F.map₂ (cell F μ (𝟙 f) t) ≫ (expand F μ f g').hom =
      (expand F μ f g).hom ≫ (F.map f ◁ F.map₂ (F.map₂ t)) ▷ F.map (μ X) := by
  rw [second]
  exact RepresentableAssociatorFoldCells.second F (μ X) (x := f) (F.map₂ t)
end
end ContextualComposition.GrothendieckStep.RepresentableKleisliGeneric
