module
public import ContextualComposition.AmbientMonadMaps
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientMonadMapRead
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open AmbientBicategory AmbientCoordinates ContextadRoutes ContextadNativeLaws ContextadOuterCharts
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
universe u v
section Generic
variable {C D : Type*} [Bicategory C] [Bicategory D] {F G : StrictPseudofunctor C D} {K : Pseudofunctor C D}
open AmbientMonadMaps
theorem app (e : F = G) (t : StrongTrans F.toPseudofunctor K) (X) : HEq ((transfer e t).app X) (t.app X) := by cases e; rfl
theorem square {X Y : C} (e : F = G) (t : StrongTrans F.toPseudofunctor K) (f : X ⟶ Y) :
    HEq ((transfer e t).naturality f) (t.naturality f) := by cases e; rfl
end Generic
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) {X Y : Obj.{u,v} B} (f : X ⟶ Y)
theorem etaApp (X : Obj.{u,v} B) : (AmbientMonadMaps.eta S d).app X = oper S (insert S d) (unitCart d) X :=
  eq_of_heq (app (AmbientIteratedFunctor.zero S) (AmbientPseudonaturality.operation S (insert S d) (unitCart d)) X)
def muApp (X : Obj.{u,v} B) :=
  app (F := action S 2) (G := (action S 1).comp (action S 1)) (K := AmbientMonadMaps.K S) (AmbientIteratedFunctor.succ S 1).symm (AmbientPseudonaturality.operation S (tensor m) m.cart) X
theorem etaSquare : HEq ((AmbientMonadMaps.eta S d).naturality f) (comparison S (insert S d) (unitCart d) f) :=
  square (AmbientIteratedFunctor.zero S) (AmbientPseudonaturality.operation S (insert S d) (unitCart d)) f
def muSquare :=
  square (F := action S 2) (G := (action S 1).comp (action S 1)) (K := AmbientMonadMaps.K S) (AmbientIteratedFunctor.succ S 1).symm (AmbientPseudonaturality.operation S (tensor m) m.cart) f
end ContextualComposition.GrothendieckStep.AmbientMonadMapRead
