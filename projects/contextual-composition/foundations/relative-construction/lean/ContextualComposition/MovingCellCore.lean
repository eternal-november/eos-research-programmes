module
public import ContextualComposition.ChartRealization
public import ContextualComposition.MovingCoordinates
@[expose] public section
namespace ContextualComposition.GrothendieckStep.MovingCell
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates
section General
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
theorem undoApp (N : C ≌ D) (F : D ⥤ E) (G : C ⥤ E) (q : N.functor ⋙ F ≅ G) (x : D) :
    (undoChart N F G q).hom.app x = F.map (N.counitIso.inv.app x) ≫ q.hom.app (N.inverse.obj x) := rfl
end General
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
abbrev A (x : X S Y) := (base S Y).obj x
abbrev I (x : X S Y) := FibreValue.incl (twice S Y) (A S Y x)
noncomputable abbrev L := read S Y ⋙ Sigma.desc (refL S Y)
noncomputable abbrev R := read S Y ⋙ Sigma.desc (refR S Y)
theorem refEq : L S Y = R S Y := congrArg (fun H => read S Y ⋙ Sigma.desc H) (funext (reference S Y))
noncomputable abbrev lObj (x : X S Y) := (I S Y x).obj ((stages S Y (A S Y x)).obj (point S Y x))
noncomputable abbrev rObj (x : X S Y) := (I S Y x).obj ((previous S Y (A S Y x)).obj (point S Y x))
noncomputable def left (x : X S Y) : lObj S Y x ≅ (L S Y).obj x := by
  let a := A S Y x
  let z := decode S Y x
  let N := nativeEquiv S Y a
  exact (I S Y x).mapIso (((stages S Y a).mapIso (N.counitIso.app (point S Y x)).symm) ≪≫ (chartEq S Y a).app z) ≪≫
    eqToIso (firstObj S Y a z.1 z.2)
noncomputable def right (x : X S Y) : rObj S Y x ≅ (R S Y).obj x := by
  let a := A S Y x
  let z := decode S Y x
  exact (I S Y x).mapIso ((eqToIso (oldChart S Y a)).symm.app z) ≪≫ eqToIso (secondObj S Y a z.1 z.2)
noncomputable abbrev leftTotal := realize (L S Y) (left S Y)
noncomputable abbrev rightTotal := realize (R S Y) (right S Y)
noncomputable def cell : leftTotal S Y ≅ rightTotal S Y := paste (eqToIso (refEq S Y)) (left S Y) (right S Y)
theorem published (a : B) : BlockCompositor.compositor S Y a =
    undoChart (nativeEquiv S Y a) (stages S Y a) (packedEquiv S Y a).functor (ChartRestriction.route S Y a) := by
  unfold BlockCompositor.compositor ofFixed ChartRestriction.route ChartRestriction.fixedCells
  rfl
end ContextualComposition.GrothendieckStep.MovingCell
