module
public import ContextualComposition.ContextadOutsideLaws
public import ContextualComposition.ContextadUnitTotal
public import ContextualComposition.ContextadActionCells
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadStandardLaws
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadLawTransport ContextadNativeLaws
open ContextadWeakAction ContextadOuterCharts ContextadUnitTotal
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (c : Constraints d m)
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B)
noncomputable def left : ContextadUnit.atBase d (LY (S := S) Y) A ⋙ ContextadCoherence.actual m Y A ≅ 𝟭 _ :=
  isoWhiskerRight (outerUnit Y d A).symm _ ≪≫ leftUnitor d m Y A c
noncomputable def right : ChainPayload.fibreMap (ContextadUnit.onPresheaf d S Y) (P.extend A) ⋙ ContextadCoherence.actual m Y A ≅ 𝟭 _ :=
  eqToIso (congrArg (· ⋙ ContextadCoherence.actual m Y A) (insideEta Y d A).symm) ≪≫ rightUnitor d m Y A c
noncomputable def assoc : ContextadCoherence.actual m (LY (S := S) Y) A ⋙ ContextadCoherence.actual m Y A ≅
    action (P.extend A) (ContextadTotal.total m Y) (over Y (tensor m)) ⋙ ContextadCoherence.actual m Y A :=
  isoWhiskerRight (outerTensor Y m A).symm _ ≪≫ associator d m Y A c ≪≫
    eqToIso (congrArg (· ⋙ ContextadCoherence.actual m Y A) (insideTensor Y m A))
end ContextualComposition.GrothendieckStep.ContextadStandardLaws
