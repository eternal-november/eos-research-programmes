module
public import ContextualComposition.MovingExpansion
@[expose] public section
namespace ContextualComposition.GrothendieckStep.MovingCell
open CategoryTheory CategoryTheory.Functor
section Assembly
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
theorem assemble (J : C ⥤ D) (K : E ⥤ C) {a d : C} {b c : E} {lo hi : D}
    (p : a ⟶ K.obj b) (e : b = c) (f : K.obj c = d) (l : J.obj (K.obj b) = lo) (r : J.obj (K.obj c) = hi) (u : lo = hi)
    {alpha : J.obj a ⟶ J.obj d} {beta : a ⟶ d} {s : J.obj a ⟶ lo} {t : hi ⟶ J.obj d}
    (h : alpha = s ≫ eqToHom u ≫ t) (hL : s = J.map p ≫ eqToHom l)
    (hR : t = eqToHom r.symm ≫ J.map (eqToHom f))
    (hN : beta = p ≫ K.map (eqToHom e) ≫ eqToHom f) : alpha = J.map beta := by
  rw [h,hL,hR,hN,eqToHom_map K e]
  exact casts J p (congrArg K.obj e) f l r u
end Assembly
end ContextualComposition.GrothendieckStep.MovingCell
