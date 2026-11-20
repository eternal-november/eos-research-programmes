module
public import ContextualComposition.RepresentableKleisliOperations
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableLayerNaturality
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open AmbientBicategory ContextadAmbientPayload ContextadWeakAction ContextadModification BoundaryPaste NativeBlocks FibreValue
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
universe u
variable {B : Type u} [Category.{u} B] {Y Z : Bᵒᵖ ⥤ Cat.{u,u}}
section Indexed
variable {K L : Type*} [Category* K] [Category* L] (r : K ⥤ L) (d : L ⥤ B) {e : K ⥤ B} (h : r ⋙ d = e)
variable (f : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)) (o : f ⋙ proj Z = proj Y)
theorem indexed : SpanPayload.totalMap Y r d h ⋙ action d f o = action e f o ⋙ SpanPayload.totalMap Z r d h := by
  apply fold_ext d Z
  · calc
      _ = SpanPayload.totalMap Y r d h ⋙ gradeProjection := congrArg (SpanPayload.totalMap Y r d h ⋙ ·) (actionGrade d f o)
      _ = gradeProjection ⋙ r := SpanPayload.total_projection Y r d h
      _ = _ := ((congrArg (· ⋙ r) (actionGrade e f o)).symm.trans
          (congrArg (action e f o ⋙ ·) (SpanPayload.total_projection Z r d h).symm))
  · calc
      _ = SpanPayload.totalMap Y r d h ⋙ NativeTrace.leaf Y d ⋙ f :=
        congrArg (SpanPayload.totalMap Y r d h ⋙ ·) (actionLeaf d f o)
      _ = NativeTrace.leaf Y e ⋙ f := congrArg (· ⋙ f) (NativeTrace.leaf_total Y r d h)
      _ = _ := (actionLeaf e f o).symm.trans
        (congrArg (action e f o ⋙ ·) (NativeTrace.leaf_total Z r d h).symm)
end Indexed
section Chart
variable {I J K L : Type*} [Category* I] [Category* J] [Category* K] [Category* L]
variable (U : I ⥤ J) (V : K ⥤ L) [U.IsIso] (p : I ⥤ K) (a : J ⥤ L)
theorem cancelChart (h : a = U.strictInv ⋙ p ⋙ V) : U ⋙ a = p ⋙ V := by
  rw [h, ← Functor.assoc]
  exact (congrArg (· ⋙ p ⋙ V) U.asIsomorphism.unit_eq.symm).trans (Functor.id_comp _)
variable {S₀ R : Type*} [Category* S₀] [Category* R]
theorem close (i : S₀ ⥤ I) (j : R ⥤ K) (v : S₀ ⥤ R) (x : S₀ ⥤ J) (y : R ⥤ L) (f : S₀ ⥤ R)
    (one : f ⋙ y = x ⋙ a) (two : x = i ⋙ U) (three : U ⋙ a = p ⋙ V)
    (four : i ⋙ p = v ⋙ j) (five : j ⋙ V = y) : f ⋙ y = v ⋙ y := by
  rw [one,two,Functor.assoc,three,← Functor.assoc,four,Functor.assoc,five]
end Chart
variable {P : Endpoints.{u,u,u,u} B} (S : P.Split) (g : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (A : B)
theorem globalLayer :
    BlockEvaluation.global S Y 1 ⋙ totalStrong (blockStrong (S := S) g 1) =
      atEndpoint g (power S 1).dest ⋙ BlockEvaluation.global S Z 1 :=
  cancelChart _ _ _ _ (AmbientBlockIteration.encodedBlock S g 1)
theorem fibreLayer :
    AmbientRoundTrip.compAt (blockStrong (S := S) g 1) A = atEndpoint g (P.extend A) := by
  apply ContextadFinal.cancelIncl (PackedFree.pow S Z 1) A _ _
  refine close (BlockEvaluation.global S Y 1) (BlockEvaluation.global S Z 1) (atEndpoint g (power S 1).dest) (totalStrong (blockStrong (S := S) g 1))
    (ContextadVertical.insertOne (S := S) A Y) (ContextadVertical.insertOne (S := S) A Z) (atEndpoint g (P.extend A))
    (incl (PackedFree.pow S Y 1) A) (incl (PackedFree.pow S Z 1) A) (AmbientRoundTrip.compAt (blockStrong (S := S) g 1) A)
    (AmbientRoundTrip.strongIncl _ A) (ContextadUnary.recognition S A Y).symm (globalLayer S g) ?_ (ContextadUnary.recognition S A Z)
  exact indexed (ContextadChart.one (P := P) A) (power S 1).dest (ContextadChart.oneEnd S A) (totalStrong g) (strongOver g)
end ContextualComposition.GrothendieckStep.RepresentableLayerNaturality
