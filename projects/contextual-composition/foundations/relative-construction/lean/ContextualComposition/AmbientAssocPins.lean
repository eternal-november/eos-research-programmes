module
public import ContextualComposition.AmbientInsideMulWeight
public import ContextualComposition.AmbientSuccessorMap
public import ContextualComposition.AmbientOutsideWeightRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientAssocPins
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
noncomputable def A (Z : Obj.{u,v} B) : obj S 3 Z ⟶ obj S 2 Z := M S (obj S 1 Z) m
noncomputable def B' (Z : Obj.{u,v} B) : obj S 3 Z ⟶ obj S 2 Z := K S (M S Z m)
noncomputable def front : obj S 3 X ⟶ obj S 3 Y :=
  K S (X := obj S 2 X) (Y := obj S 2 Y) (K S (X := obj S 1 X) (Y := obj S 1 Y) (K S f))
theorem triple : front (S := S) f = AmbientBicategory.map S 3 f :=
  AmbientSuccessorMap.lift (n := 2) f (K S (K S f)) (twice S f)
theorem eA (Z : Obj.{u,v} B) : global (S := S) (i := 3) (j := 2) (underlying Z) (firstTwo m) = tot (A m Z) := outerM S Z m
theorem eB (Z : Obj.{u,v} B) : global (S := S) (i := 3) (j := 2) (underlying Z) (lastTwo m) = tot (B' m Z) := innerM S Z m
end ContextualComposition.GrothendieckStep.AmbientAssocPins
