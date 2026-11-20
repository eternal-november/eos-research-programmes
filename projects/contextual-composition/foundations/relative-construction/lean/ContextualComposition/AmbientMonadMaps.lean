module
public import ContextualComposition.AmbientPseudonaturality
public import ContextualComposition.AmbientIteratedFunctor
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientMonadMaps
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open AmbientBicategory ContextadModification NativeBlocks ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientCoordinates
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
def transfer {C D : Type*} [Bicategory C] [Bicategory D] {F G : StrictPseudofunctor C D} {K : Pseudofunctor C D} (e : F = G) (t : StrongTrans F.toPseudofunctor K) : StrongTrans G.toPseudofunctor K :=
  Eq.mp (congrArg (fun Q : StrictPseudofunctor C D => StrongTrans Q.toPseudofunctor K) e) t
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
noncomputable abbrev K := (action S 1).toPseudofunctor
noncomputable abbrev II := (StrictPseudofunctor.id (Obj.{u,v} B)).toPseudofunctor
noncomputable abbrev KK := ((action S 1).comp (action S 1)).toPseudofunctor
noncomputable def eta (d : ContextadUnit.Data P) : StrongTrans (II (B := B)) (K S) :=
  transfer (F := action S 0) (K := K S) (AmbientIteratedFunctor.zero S) <|
  AmbientPseudonaturality.operation S (insert S d) (unitCart d)
noncomputable def mu (m : ContextadTotal.Native S) : StrongTrans (KK S) (K S) :=
  transfer (F := action S 2) (K := K S) (AmbientIteratedFunctor.succ S 1).symm <|
  AmbientPseudonaturality.operation S (tensor m) m.cart
end ContextualComposition.GrothendieckStep.AmbientMonadMaps
