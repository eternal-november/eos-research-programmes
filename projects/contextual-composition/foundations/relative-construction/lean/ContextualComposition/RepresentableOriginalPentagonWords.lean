module
public import ContextualComposition.RepresentableKleisliPentagonPaths
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableOriginalPentagonWords
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open RepresentableKleisliOriginal RepresentableKleisliPentagonPaths RepresentablePentagonWord
open RepresentableKleisli
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
section Abstract
variable {C : Type*} [Bicategory C] {a b c d : C} {m m' m'' : a ⟶ b} {n n' : b ⟶ c} (q : c ⟶ d)
variable (A : n ≫ q ≅ n' ≫ q) (B : m ≫ n ≅ m' ≫ n) (R : m' ≫ n' ≅ m'' ≫ n') (D : m ≫ n' ≅ m'' ≫ n)
theorem read
    (h : (whiskerRightIso B q ≪≫ middle m' n q A ≪≫ whiskerRightIso R q).hom =
      (middle m n q A ≪≫ whiskerRightIso D q ≪≫ middle m'' n q A).hom) :
    outerLong A B R = outerShort D A := by
  apply Iso.ext
  exact h
end Abstract
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable (Z : Obj.{u,u} B)
set_option linter.defProp false in
def good :=
  read (C := Obj.{u,u} B) (M.{u,u} S Z T.mult) (assocIso.{u,u} T Z)
    (assocIso.{u,u} T (obj.{u,u} S 1 Z)) (foldMap (action.{u,u} S 1) (assocIso.{u,u} T Z))
    (squareM.{u,u} S T.mult (M.{u,u} S Z T.mult)).symm (T.laws.pentagon Z)
variable {U V X Y Z₀ : B}
variable (f : KH S U V) (g : KH S V X) (h : KH S X Y) (i : KH S Y Z₀)
set_option linter.defProp false in
def core :=
  RepresentablePentagonCore.core (D T h).symm (D T i).symm (D T (K S i)).symm
    (foldMap (action S 1) (D T i)).symm (D T (μ T (yObj Z₀))).symm
    (a T (yObj Y)) (a T (yObj Z₀)) (a T (KObj S Z₀)) (foldMap (action S 1) (a T (yObj Z₀)))
    (RepresentablePentagonCorner.original T i) (good T (yObj Z₀))
theorem words :
    wordLong (action S 1) (μ T) (D T) (a T) f g h i =
    wordShort (action S 1) (μ T) (D T) (a T) f g h i :=
  congrArg (fun v => bridge (action S 1) (μ T) f g h i v
    (front (action S 1) (μ T) f g h i) (back (action S 1) (μ T) f g h i)) (core T h i)
end ContextualComposition.GrothendieckStep.RepresentableOriginalPentagonWords
