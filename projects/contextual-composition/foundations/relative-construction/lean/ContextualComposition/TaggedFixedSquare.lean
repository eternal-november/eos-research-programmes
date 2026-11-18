module
public import ContextualComposition.TaggedTripleCover
public import ContextualComposition.TaggedTripleFaces
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedFixedSquare
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked BlockEvaluation TripleEvaluation ChartRealization
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (n m k : Nat)
abbrev tripleInc := ChainPayload.layerMap (put S Y (m,k)) S n ≫ PackedFree.inc S (twice S Y) n
abbrev packOut := ChainPayload.fibreMap (tripleInc S Y n m k) (𝟭 B)
noncomputable abbrev fa := whiskerRight (SuffixCell.leftFace S Y n m k) (packOut S Y n m k)
noncomputable abbrev fb := whiskerRight (SuffixCell.rightFace S Y n m k) (packOut S Y n m k)
noncomputable abbrev fs := whiskerRight (eqToHom (stages S Y n m k)) (packOut S Y n m k)
noncomputable abbrev ft := whiskerRight (eqToHom (fixedAssociativity S Y n m k)) (packOut S Y n m k)
section General
variable {A C D : Type*} [Category* A] [Category* C] [Category* D]
theorem packSquare {F G H I : A ⥤ C} (a : F ⟶ G) (b : H ⟶ I) (s : F ⟶ H) (t : G ⟶ I) (K : C ⥤ D)
    (h : a ≫ t = s ≫ b) : whiskerRight a K ≫ whiskerRight t K = whiskerRight s K ≫ whiskerRight b K := by
  ext x
  exact (K.map_comp _ _).symm.trans ((congrArg K.map (NatTrans.congr_app h x)).trans (K.map_comp _ _))
end General
theorem fixed : fa S Y n m k ≫ ft S Y n m k = fs S Y n m k ≫ fb S Y n m k :=
  packSquare _ _ _ _ (packOut S Y n m k) (SuffixCell.square S Y n m k)
end ContextualComposition.GrothendieckStep.TaggedFixedSquare
