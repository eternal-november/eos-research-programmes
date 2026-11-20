module
public import ContextualComposition.AmbientUnitSquareCore
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
set_option linter.defProp false in
def installed (Z : Obj.{u,v} B) (u : obj S 1 Z ⟶ obj S 2 Z) (j : global Z r = tot u) :=
  route S Z (i := 1) (j := 2) (k := 1) r (tensor m) (cart m r c) m.cart u j
set_option linter.defProp false in
def seam (h : RRead (i := 1) (j := 2) S f s r) :=
  toBend (i := 1) (j := 1) S f rfl (comp r (tensor m)) (cart m r c)
    (installed m r c X a e) (installed m r c Y b w) (serial s (squareM S m f)) (reads f m r e s h)
end ContextualComposition.GrothendieckStep.AmbientUnitSquare
