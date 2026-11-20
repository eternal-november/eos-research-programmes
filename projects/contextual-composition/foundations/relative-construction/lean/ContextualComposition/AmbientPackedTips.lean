module
public import ContextualComposition.AmbientInputIndex
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientPackedTips
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadOuterRigidity ContextadDisjointCut AmbientChosenTail
open ContextadSchedule ContextadModification ContextadAmbientPayload
open AmbientBicategory AmbientCoordinates ContextadWeakWeight ContextadWeakAction ContextadCellWhisker AmbientTerminalCones AmbientHorizontalFrames
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1) (pg : gradeCart g)
def Chosen (Y : Obj.{u,v} B) {a b : Total (underlying Y) (𝟭 B)} (v : a ⟶ b) : Prop := Pure (payloadMap v)
theorem atChosen (Y : Obj.{u,v} B) (z : Raw S Y 2)
    {a b : Total (underlying Y) (𝟭 B)} (v : a ⟶ b)
    (t : b = (leafAt (underlying Y) (E (S := S) 2)).obj z)
    (g : Aligned (gradeMap v) (f.leg.app (grade (underlying Y) (E (S := S) 2) z)))
    (p : Chosen Y v) : Aligned v (tipAt f Y z) :=
  ContextadChosenCone.alignChosen _ _ t g p (pureId _)
theorem inputPure (x : Raw S X 4) : Chosen (obj S 2 X) (fromRaw X f x) := by
  unfold Chosen fromRaw wt chart
  exact packedWide (underlying X) f x
set_option linter.defProp false in
def inputTip (x : Raw S X 4) :=
  atChosen f (obj S 2 X) ((I (S := S) X).obj x) (fromRaw X f x)
    (Functor.congr_obj (inputLeaf (S := S) X).symm x)
    (baseIn X f x)
    (inputPure X f x)
end
end ContextualComposition.GrothendieckStep.AmbientPackedTips
