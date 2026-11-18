module
public import ContextualComposition.MovingCellCore
@[expose] public section
namespace ContextualComposition.GrothendieckStep.MovingCell
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates
section General
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
theorem pasteApp (F G : C ⥤ D) (e : F = G) {X Z : C → D} (l : ∀ x, X x ≅ F.obj x) (r : ∀ x, Z x ≅ G.obj x) (x : C) :
    (paste (eqToIso e) l r).hom.app x = (l x).hom ≫ eqToHom (Functor.congr_obj e x) ≫ (r x).inv := by
  simp [paste,gauge,eqToHom_app]
  rfl
theorem alignedHom (J : C ⥤ D) {a b c : C} (p : a ≅ b) (q : b ≅ c) {u : D} (h : J.obj c = u) :
    (J.mapIso (p ≪≫ q) ≪≫ eqToIso h).hom = J.map (p.hom ≫ q.hom) ≫ eqToHom h := rfl
theorem casts (J : C ⥤ D) {a b c d : C} (p : a ⟶ b) (e : b = c) (f : c = d)
    {u v : D} (l : J.obj b = u) (r : J.obj c = v) (h : u = v) :
    ((J.map p ≫ eqToHom l) ≫ eqToHom h ≫ eqToHom r.symm ≫ J.map (eqToHom f)) =
      J.map (p ≫ eqToHom e ≫ eqToHom f) := by subst c; subst d; subst u; subst v; simp
end General
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
abbrev lHom (x : X S Y) :=
  alignedHom (I S Y x) ((stages S Y (A S Y x)).mapIso ((nativeEquiv S Y (A S Y x)).counitIso.app (point S Y x)).symm)
    ((chartEq S Y (A S Y x)).app (decode S Y x)) (firstObj S Y (A S Y x) (decode S Y x).1 (decode S Y x).2)
theorem rInv (x : X S Y) : (right S Y x).inv =
    eqToHom (secondObj S Y (A S Y x) (decode S Y x).1 (decode S Y x).2).symm ≫
      (I S Y x).map (eqToHom (Functor.congr_obj (oldChart S Y (A S Y x)) (decode S Y x))) := by
  change _ ≫ (I S Y x).map ((eqToHom (oldChart S Y (A S Y x))).app (decode S Y x)) = _
  simp only [eqToHom_app,eqToIso.inv]
end ContextualComposition.GrothendieckStep.MovingCell
