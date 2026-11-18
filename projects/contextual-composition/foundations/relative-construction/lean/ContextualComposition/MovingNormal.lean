module
public import ContextualComposition.MovingCellCore
@[expose] public section
namespace ContextualComposition.GrothendieckStep.MovingCell
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates
section General
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
theorem undoAppOf (N : C ≌ D) (F : D ⥤ E) (G : C ⥤ E) (q : N.functor ⋙ F ≅ G) (u : F ≅ N.inverse ⋙ G)
    (h : u = undoChart N F G q) (x : D) : u.hom.app x = F.map (N.counitIso.inv.app x) ≫ q.hom.app (N.inverse.obj x) := by
  subst u
  exact undoApp N F G q x
theorem splice {w x y z : C} {f : w ⟶ z} {a : w ⟶ x} {q : x ⟶ z} {b : x ⟶ y} {c : y ⟶ z}
    (h : f = a ≫ q) (k : q = b ≫ c) : f = (a ≫ b) ≫ c := by rw [h,k,Category.assoc]
theorem normalFrom (N : C ≌ D) (F : D ⥤ E) (G : C ⥤ E) (q : N.functor ⋙ F ≅ G) (u : F ≅ N.inverse ⋙ G)
    (h : u = undoChart N F G q) (x : D) {a : E} (b : F.obj (N.functor.obj (N.inverse.obj x)) ⟶ a) (c : a ⟶ G.obj (N.inverse.obj x))
    (k : q.hom.app (N.inverse.obj x) = b ≫ c) : u.hom.app x = (F.map (N.counitIso.inv.app x) ≫ b) ≫ c :=
  splice (undoAppOf N F G q u h x) k
theorem normalFamily (N : C ≌ D) (F : D ⥤ E) (G : C ⥤ E) (q : N.functor ⋙ F ≅ G) (u : F ≅ N.inverse ⋙ G)
    (h : u = undoChart N F G q) (a : C → E) (b : ∀ z, F.obj (N.functor.obj z) ⟶ a z) (c : ∀ z, a z ⟶ G.obj z)
    (k : ∀ z, q.hom.app z = b z ≫ c z) (x : D) : u.hom.app x = (F.map (N.counitIso.inv.app x) ≫ b (N.inverse.obj x)) ≫ c (N.inverse.obj x) :=
  normalFrom N F G q u h x _ _ (k _)
end General
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (a : B)
noncomputable abbrev zz (y : W S Y a) := (nativeEquiv S Y a).inverse.obj y
noncomputable abbrev pfx (y : W S Y a) := (stages S Y a).map ((nativeEquiv S Y a).counitIso.inv.app y) ≫ (chartEq S Y a).hom.app (zz S Y a y)
theorem routeApp (z : Σ i, coords S Y a i) :
    (ChartRestriction.route S Y a).hom.app z =
      (chartEq S Y a).hom.app z ≫ (pack S Y a z.1).map (eqToHom (Functor.congr_obj (BlockCompositor.fixedCompositor S Y a z.1.1 z.1.2) z.2)) ≫
      eqToHom (Functor.congr_obj (oldChart S Y a) z) := by
  rcases z with ⟨i,y⟩
  change (chartEq S Y a).hom.app ⟨i,y⟩ ≫ (pack S Y a i).map ((eqToHom (BlockCompositor.fixedCompositor S Y a i.1 i.2)).app y) ≫
    (eqToHom (oldChart S Y a)).app ⟨i,y⟩ = _
  simp only [eqToHom_app]
abbrev descApp (y : W S Y a) :=
  undoAppOf (nativeEquiv S Y a) (stages S Y a) (packedEquiv S Y a).functor (ChartRestriction.route S Y a) (BlockCompositor.compositor S Y a) (published S Y a) y
abbrev normal :=
  normalFamily (nativeEquiv S Y a) (stages S Y a) (packedEquiv S Y a).functor (ChartRestriction.route S Y a)
    (BlockCompositor.compositor S Y a) (published S Y a) (CutCompositor.chart S Y a).obj
    (fun z => (chartEq S Y a).hom.app z)
    (fun z => (pack S Y a z.1).map (eqToHom (Functor.congr_obj (BlockCompositor.fixedCompositor S Y a z.1.1 z.1.2) z.2)) ≫
      eqToHom (Functor.congr_obj (oldChart S Y a) z))
    (routeApp S Y a)
end ContextualComposition.GrothendieckStep.MovingCell
