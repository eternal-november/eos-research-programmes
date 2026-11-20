module
public import ContextualComposition.RepresentableFibreCells
public import ContextualComposition.RepresentableCompositionComparison
public import ContextualComposition.RepresentableLayerCells
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableCompositionCells
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor CategoryTheory.Bicategory Opposite
open AmbientBicategory AmbientCoherentPseudomonad AmbientHorizontalFrames AmbientRoundTrip
open RepresentableKleisli RepresentableNativeComposition ContextadAmbientPayload AmbientBlockCells
open WordTrace AmbientCellTrace RepresentableLayerNaturality
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable {A D E : B} (T : Data S)
variable {f f' : KH S A D} {g g' : KH S D E}
variable (t : f ⟶ f') (k : g ⟶ g')
noncomputable def beforeFold : f ≫ AmbientBicategory.map S 1 g ⟶ f' ≫ AmbientBicategory.map S 1 g' :=
  (t ▷ AmbientBicategory.map S 1 g) ≫ f' ◁ AmbientBicategory.cell S 1 k
def atFirst : row f ⟶ row f' := (rows (S := S) A D).map t
noncomputable def atSecond : (compAt (AmbientBicategory.map S 1 g).hom A).obj (row f') ⟶ (compAt (AmbientBicategory.map S 1 g').hom A).obj (row f') :=
  component (AmbientBicategory.cell S 1 k) A (row f')
noncomputable def compositionImage :=
  (compAt (M S (yObj E) T.mult).hom A).map
    ((compAt (AmbientBicategory.map S 1 g).hom A).map (atFirst t) ≫ atSecond k)
noncomputable def actualImage : Edge (Row (P := P) A E) :=
  edge ((rows (S := S) A E).map (composeCell T t k))
noncomputable def imageEdge : Edge (Row (P := P) A E) := edge (compositionImage T t k)
set_option linter.defProp false in
def firstEvaluation := congrArg edge (RepresentableFibreCells.rowMap (S := S) (J := A) (D := E) (composeCell T t k))
set_option linter.defProp false in
def secondEvaluation := congrArg edge (RepresentableFibreCells.serial (U := yObj A) (V := KObj S D)
  (W := AmbientBicategory.obj.{u,u} S 2 (yObj E)) (R := KObj S E) A (Discrete.mk (𝟙 A)) t (AmbientBicategory.cell S 1 k) (M S (yObj E) T.mult))
theorem actualCell : actualImage T t k = imageEdge T t k := (firstEvaluation T t k).trans (secondEvaluation T t k)
theorem firstColumn :
    Edge.map (compAt (AmbientBicategory.map S 1 g).hom A) (edge (atFirst t)) =
      Edge.map (atEndpoint g.hom (P.extend A)) (edge (atFirst t)) :=
  congrArg (fun F => Edge.map F (edge (atFirst t))) (fibreLayer S g.hom A)
theorem secondColumn :
    edge (atSecond (f' := f') k) =
      edge ((endpointCell (P.extend A) k.hom.as).app (row f')) :=
  RepresentableLayerCells.localCell S A k.hom.as (row f')
end ContextualComposition.GrothendieckStep.RepresentableCompositionCells
