module
public import ContextualComposition.AmbientUnitDescent
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientUnitSquare
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open AmbientBoundaryReduction AmbientSquareBridge ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) (m : ContextadTotal.Native S)
variable {a : obj S 1 X ⟶ obj S 2 X} {b : obj S 1 Y ⟶ obj S 2 Y}
variable (r : Map S 1 2) (c : Cell (comp r (tensor m)) (ContextadRoutes.identity 1))
variable (e : global X r = tot a) (w : global Y r = tot b)
variable (s : K S f ≫ b ≅ a ≫ K S (X := obj S 1 X) (Y := obj S 1 Y) (K S f))
theorem naturality (h : RRead (i := 1) (j := 2) S f s r) : Result f m r c e w s :=
  replace (seam f m r c e w s h) (idTarget S f 1) (carried f m r c e w)
end ContextualComposition.GrothendieckStep.AmbientUnitSquare
