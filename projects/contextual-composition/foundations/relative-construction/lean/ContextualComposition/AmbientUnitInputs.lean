module
public import ContextualComposition.AmbientUnitSquare
public import ContextualComposition.AmbientRightWeight
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientUnitInputs
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
structure Boundary (r : Map S 1 2) where
  a : obj S 1 X ⟶ obj S 2 X
  b : obj S 1 Y ⟶ obj S 2 Y
  e : global X r = tot a
  w : global Y r = tot b
  s : K S f ≫ b ≅ a ≫ K S (K S f)
  h : RRead (i := 1) (j := 2) S f s r
variable (m : ContextadTotal.Native S) {r : Map S 1 2} (v : Boundary f r)
variable (c : Cell (comp r (tensor m)) (ContextadRoutes.identity 1))
def Observed : Prop := AmbientUnitSquare.Result f m r c v.e v.w v.s
theorem assemble : Observed f m v c :=
  AmbientUnitSquare.naturality f m r c v.e v.w v.s v.h
end ContextualComposition.GrothendieckStep.AmbientUnitInputs
