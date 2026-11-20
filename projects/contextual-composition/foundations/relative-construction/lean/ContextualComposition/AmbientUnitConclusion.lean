module
public import ContextualComposition.AmbientUnitSquare
public import ContextualComposition.AmbientRightWeight
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientUnitConclusion
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open AmbientBoundaryReduction ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
open AmbientUnitSquare
variable (m : ContextadTotal.Native S) {a : obj S 1 X ⟶ obj S 2 X} {b : obj S 1 Y ⟶ obj S 2 Y}
variable (r : Map S 1 2) (c : Cell (comp r (tensor m)) (ContextadRoutes.identity 1))
variable (e : global X r = tot a) (w : global Y r = tot b)
variable (s u : K S f ≫ b ≅ a ≫ K S (X := obj S 1 X) (Y := obj S 1 Y) (K S f))
variable (L : a ≫ M S X m ≅ 𝟙 _) (R : b ≫ M S Y m ≅ 𝟙 _)
def SquareAt : Prop := Square (serial u (squareM S m f)) (AmbientHorizontalNaturality.identity (K S f)) L R
theorem conclude (t : s = u) (l : constr m r c X a e = L) (k : constr m r c Y b w = R)
    (h : RRead (i := 1) (j := 2) S f s r) : SquareAt f m u L R := by
  subst u; subst L; subst R; exact AmbientUnitSquare.naturality f m r c e w s h
end ContextualComposition.GrothendieckStep.AmbientUnitConclusion
