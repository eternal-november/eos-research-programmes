module
public import ContextualComposition.AmbientMultiplicationSpoke
public import ContextualComposition.AmbientSquareGuard
public import ContextualComposition.AmbientBoundaryReduction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientGuardSpoke
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open AmbientBoundaryReduction AmbientSquareBridge ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1550000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) (m : ContextadTotal.Native S)
variable {i : Nat}
variable {z : obj S i X ⟶ obj S i Y} (hz : z = AmbientBicategory.map S i f)
variable {a : obj S i X ⟶ obj S 2 X} {b : obj S i Y ⟶ obj S 2 Y}
variable (r : Map S i 2) (p : gradeCart (S := S) (i := i) (j := 1) (comp (i := i) (j := 2) (k := 1) r (tensor m)))
variable (e : global (S := S) (i := i) (j := 2) (underlying X) r = tot (V := obj S i X) (W := obj S 2 X) a) (w : global (S := S) (i := i) (j := 2) (underlying Y) r = tot (V := obj S i Y) (W := obj S 2 Y) b)
variable (s : z ≫ b ≅ a ≫ K S (X := obj S 1 X) (Y := obj S 1 Y) (K S f))
set_option linter.defProp false in
def seam (h : AmbientSquareGuard.Guard (i := i) (j := 2) f r s) :=
  AmbientMultiplicationSpoke.seam (i := i) (a := a) (b := b) f m hz r p e w s (AmbientSquareGuard.unpack (i := i) (j := 2) f r s h)
end ContextualComposition.GrothendieckStep.AmbientGuardSpoke
