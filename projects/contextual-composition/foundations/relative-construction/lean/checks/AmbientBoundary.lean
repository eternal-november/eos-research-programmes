import ContextualComposition.ContextadAmbientIsoMod
import ContextualComposition.ContextadCoherentDetection
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks ContextadAmbientPayload ContextadRoutes ContextadLawTransport
open CategoryTheory.Pseudofunctor ContextadModification ContextadNativeLaws ContextadOuterCharts
namespace AmbientBoundary
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {Y Z W : PackedCuts.Psh.{u,max u v,u,v} B}
variable (a t : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (b : StrongTrans Z.toPseudofunctor' W.toPseudofunctor')
abbrev Hom2 := StrongTrans.Modification (layerStrong S a) (layerStrong S t)
abbrev ambientCompositor := ModIso ((layerStrong S a).vcomp (layerStrong S b)) (layerStrong S (a.vcomp b))
abbrev blockIterator := ModIso (layerStrong S (layerStrong S a)) (blockStrong (S := S) a 2)
variable (m : ContextadTotal.Native S) (d : ContextadUnit.Data P)
noncomputable abbrev eta (Q : PackedCuts.Psh.{u,max u v,u,v} B) := nativeStrong Q (insert S d) (unitCart d)
abbrev unitBoundary := ModIso (a.vcomp (eta S d Z)) ((eta S d Y).vcomp (layerStrong S a))
abbrev tensorBoundary := ModIso ((layerStrong S (layerStrong S a)).vcomp (ContextadStrong.multiplication m Z)) ((ContextadStrong.multiplication m Y).vcomp (layerStrong S a))
#check layerComp
#check weakOperationIso
#check unitBoundary
#check tensorBoundary
#check_failure (weakOperationIso a (tensor m) m.cart : tensorBoundary S a m)
#check_failure (weakOperationIso a (insert S d) (unitCart d) : unitBoundary S a d)
end AmbientBoundary
