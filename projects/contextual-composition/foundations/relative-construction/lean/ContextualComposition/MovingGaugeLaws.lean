module
public import ContextualComposition.MovingNormal
public import ContextualComposition.MovingExpansion
@[expose] public section
namespace ContextualComposition.GrothendieckStep.MovingCell
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
noncomputable abbrev lFrame (x : X S Y) :=
  (I S Y x).map (pfx S Y (A S Y x) (point S Y x)) ≫ eqToHom (firstObj S Y (A S Y x) (decode S Y x).1 (decode S Y x).2)
theorem leftLaw (x : X S Y) : (left S Y x).hom = lFrame S Y x := by
  unfold left lFrame pfx zz decode
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, eqToIso.hom]
end ContextualComposition.GrothendieckStep.MovingCell
