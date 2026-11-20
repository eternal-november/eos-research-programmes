module
public import ContextualComposition.RepresentableOriginalPentagonWords
public import ContextualComposition.RepresentableKleisliPentagonShort
public import ContextualComposition.RepresentableKleisliPentagonLong
public import ContextualComposition.RepresentableMultiplicationComposition
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliPentagon
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open AmbientBicategory AmbientCoherentPseudomonad AmbientHorizontalFrames AmbientHorizontalDiagrams
open RepresentableKleisli RepresentableKleisliConstraints RepresentableKleisliOriginal
open RepresentableKleisliPentagonPaths RepresentableMultiplicationPaste
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
theorem operationComp {X Y Z : Obj.{u,u} B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    D T (f ≫ g) = paste (RepresentableKleisliPentagonShort.comp₂ (action S 1) f g)
      ((action S 1).map_comp f g).symm (D T f) (D T g) :=
  RepresentableMultiplicationComposition.original T f g
variable {U V X Y Z : B}
variable (f : KH S U V) (g : KH S V X) (h : KH S X Y) (i : KH S Y Z)
set_option linter.defProp false in
def longRead :=
  RepresentableKleisliPentagonLong.normalize (U := yObj U) (V := yObj V) (X := yObj X) (Y := yObj Y) (Z := yObj Z)
    (action S 1) (μ T) (D T) (a T) f g h i
set_option linter.defProp false in
def shortRead :=
  RepresentableKleisliPentagonShort.normalize (U := yObj U) (V := yObj V) (X := yObj X) (Y := yObj Y) (Z := yObj Z)
    (action S 1) (μ T) (D T) (a T) (operationComp T) f g h i
theorem comparison :
    originalLong (action S 1) (μ T) (D T) (a T) f g h i =
    originalShort (action S 1) (μ T) (D T) (a T) f g h i :=
  (longRead T f g h i).trans ((RepresentableOriginalPentagonWords.words T f g h i).trans (shortRead T f g h i).symm)
abbrev Assocs :=
  ∀ {U V X Y : B} (f : KH S U V) (g : KH S V X) (h : KH S X Y),
    compose T (compose T f g) h ≅ compose T f (compose T g h)
noncomputable def genericBend : Assocs T := fun {_ _ _ _} f g h =>
  RepresentableKleisliGeneric.bend (action S 1) (μ T) (D T) (a T) f g h
noncomputable def oldBend : Assocs T := fun {_ _ _ _} f g h => reassociate T f g h
theorem family : (@genericBend B _ P S T) = (@oldBend B _ P S T) := by
  funext U V W X f g h
  exact bendPin T f g h
noncomputable def leftPath (A₀ : Assocs T) :=
  whiskerRightIso (whiskerRightIso (A₀ f g h) (K S i)) (M S (yObj Z) T.mult) ≪≫
    A₀ f (compose T g h) i ≪≫
      whiskerRightIso (whiskerLeftIso f ((action S 1).map₂Iso (A₀ g h i))) (M S (yObj Z) T.mult)
noncomputable def rightPath (A₀ : Assocs T) :=
  A₀ (compose T f g) h i ≪≫ A₀ f g (compose T h i)
theorem exactIso : leftPath T f g h i (oldBend T) = rightPath T f g h i (oldBend T) := by
  have H : leftPath T f g h i (genericBend T) = rightPath T f g h i (genericBend T) := comparison T f g h i
  exact (congrArg (leftPath T f g h i) (family T)).symm.trans
    (H.trans (congrArg (rightPath T f g h i) (family T)))
theorem secondCell {V W X : B} (r : KH S V W) {s s' : KH S W X} (t : s ⟶ s') :
    composeCell T (𝟙 r) t = (r ◁ (action S 1).map₂ t) ▷ M S (yObj X) T.mult := by
  unfold composeCell
  rw [id_whiskerRight,Category.id_comp]
  rfl
theorem original :
    composeCell T (reassociate T f g h).hom (𝟙 i) ≫ (reassociate T f (compose T g h) i).hom ≫
      composeCell T (𝟙 f) (reassociate T g h i).hom =
    (reassociate T (compose T f g) h i).hom ≫ (reassociate T f g (compose T h i)).hom := by
  rw [RepresentableAssociatorPrefix.first,secondCell]
  exact congrArg Iso.hom (exactIso T f g h i)
end ContextualComposition.GrothendieckStep.RepresentableKleisliPentagon
