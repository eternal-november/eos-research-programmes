module
public import ContextualComposition.MovingGaugeLaws
@[expose] public section
namespace ContextualComposition.GrothendieckStep.MovingCell
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
noncomputable abbrev nFrame (x : X S Y) :=
  let a := A S Y x
  let z := decode S Y x
  pfx S Y a (point S Y x) ≫ (pack S Y a z.1).map (eqToHom (Functor.congr_obj (BlockCompositor.fixedCompositor S Y a z.1.1 z.1.2) z.2)) ≫ eqToHom (Functor.congr_obj (oldChart S Y a) z)
theorem priorLaw (x : X S Y) : (BlockCompositor.compositor S Y (A S Y x)).hom.app (point S Y x) = nFrame S Y x := by
  unfold nFrame pfx zz decode
  exact normal S Y (A S Y x) (point S Y x)
noncomputable abbrev cFrame (x : X S Y) :=
  (left S Y x).hom ≫ eqToHom (Functor.congr_obj (refEq S Y) x) ≫ (right S Y x).inv
theorem cellLaw (x : X S Y) : (cell S Y).hom.app x = cFrame S Y x := by
  unfold cell cFrame
  exact pasteApp (L S Y) (R S Y) (refEq S Y) (left S Y) (right S Y) x
end ContextualComposition.GrothendieckStep.MovingCell
