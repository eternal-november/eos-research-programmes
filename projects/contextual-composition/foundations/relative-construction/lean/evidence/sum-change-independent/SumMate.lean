import ContextualComposition.SumChange
open CategoryTheory CategoryTheory.Functor
open ContextualComposition.GrothendieckStep.SumChange
example {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (L : C ≌ D) (M : E ≌ F) {s : C ⥤ E} {t : D ⥤ F} (h : L.functor ⋙ t ≅ s ⋙ M.functor) (x : D) :
    (inverseSquare L M h).hom.app x =
      M.unitIso.hom.app (s.obj (L.inverse.obj x)) ≫
        M.inverse.map (h.inv.app (L.inverse.obj x)) ≫
        M.inverse.map (t.map (L.counitIso.hom.app x)) := by
  simp [inverseSquare, Iso.inverseCompIso, Iso.compInverseIso, Category.assoc]
