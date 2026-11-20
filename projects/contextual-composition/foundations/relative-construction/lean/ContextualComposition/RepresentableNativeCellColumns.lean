module
public import ContextualComposition.RepresentableCompositionCells
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableNativeCellColumns
open CategoryTheory CategoryTheory.Functor Opposite FibreValue TelescopeSquares
open CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoherentPseudomonad AmbientHorizontalFrames AmbientRoundTrip
open RepresentableKleisli RepresentableNativeComposition RepresentableCompositionCells ContextadAmbientPayload AmbientBlockCells
open AmbientCellTrace WordTrace ContextadWeakAction
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable {A D E : B}
variable (T : Data S)
theorem lastColumn (z : Edge ((underlying.{u,u} (obj.{u,u} S 2 (yObj E))).obj (op A))) :
    Edge.map (compAt (M S (yObj E) T.mult).hom A) z =
      Edge.map (ContextadTensor.binary (ContextadSpecialize.data T.mult) (RepresentableYoneda.rep E) A) z :=
  congrArg (fun F => Edge.map F z) (RepresentableKleisliOperations.mulAt T (yObj E) A)
variable {x x' : Row (P := P) A D} {y y' : Row (P := P) D E}
variable (a : x ⟶ x') (b : y ⟶ y')
theorem evalLifting (x : Row (P := P) A D) {z : Row (P := P) A D} (a : x ⟶ z) :
    Edge.map ((lift (S := S) A D) ⋙ rows (S := S) A D) (edge a) = edge a :=
  congrArg (fun F => Edge.map F (edge a))
    (RepresentableYoneda.rightInverse (underlying.{u,u} (KObj S D)) A)
noncomputable def leafPart :=
  edge ((endpointCell (P.extend A) ((lift (S := S) D E).map b).hom.as).app (x' : Row (P := P) A D))
def reindexed : Edge (Row (P := P) ((P.extend A).obj (grade _ _ x')) E) :=
  Edge.map (P.baseRestrict (RepresentableYoneda.rep E) (body x')) (edge b)
theorem canonicalLeaf :
    Edge.map (NativeTrace.leaf (underlying.{u,u} (KObj S E)) (P.extend A)) (leafPart (S := S) (x' := x') b) =
      Edge.map (incl (underlying.{u,u} (KObj S E)) ((P.extend A).obj (grade _ _ x'))) (reindexed (x' := x') b) :=
  congrArg Prod.snd (RepresentableLayerCells.localRead A ((lift (S := S) D E).map b).hom.as x')
end ContextualComposition.GrothendieckStep.RepresentableNativeCellColumns
