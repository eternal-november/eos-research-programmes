module
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientHorizontalNaturality
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames AmbientHorizontalDiagrams
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
section General
variable {C : Type*} [Bicategory C] {x y z x' y' z' : C} {a : x ⟶ x'} {b : y ⟶ y'} {c : z ⟶ z'}
variable {p : x ⟶ y} {q : y ⟶ z} {p' : x' ⟶ y'} {q' : y' ⟶ z'}
def serial (s : a ≫ p' ≅ p ≫ b) (t : b ≫ q' ≅ q ≫ c) : a ≫ (p' ≫ q') ≅ (p ≫ q) ≫ c :=
  (α_ a p' q').symm ≪≫ whiskerRightIso s q' ≪≫ (α_ p b q') ≪≫ whiskerLeftIso p t ≪≫ (α_ p q c).symm
def identity (a : x ⟶ x') : a ≫ 𝟙 _ ≅ 𝟙 _ ≫ a := (ρ_ a) ≪≫ (λ_ a).symm
abbrev Square {u : x ⟶ y} {v : x' ⟶ y'} (s : a ≫ p' ≅ p ≫ b) (t : a ≫ v ≅ u ≫ b) (m : p ≅ u) (n : p' ≅ v) : Prop :=
  a ◁ n.hom ≫ t.hom = s.hom ≫ m.hom ▷ b
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (c : Constraints d m)
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
noncomputable abbrev etaK := squareE S d (K S f)
noncomputable abbrev kEta := foldMap (action S 1) (squareE S d f)
noncomputable abbrev muK := squareM S m (K S f)
noncomputable abbrev kMu := foldMap (action S 1) (squareM S m f)
abbrev Left : Prop := Square (serial (etaK S d f) (squareM S m f)) (identity (K S f)) (left S X d m c) (left S Y d m c)
abbrev Right : Prop := Square (serial (kEta S d f) (squareM S m f)) (identity (K S f)) (right S X d m c) (right S Y d m c)
abbrev Assoc : Prop := Square (serial (muK S m f) (squareM S m f)) (serial (kMu S m f) (squareM S m f)) (assoc S X d m c) (assoc S Y d m c)
end ContextualComposition.GrothendieckStep.AmbientHorizontalNaturality
