module
public import ContextualComposition.TripleCuts
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ChartRestriction
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor
set_option backward.isDefEq.respectTransparency false
section General
variable {C D R : Type*} [Category* C] [Category* D] [Category* R]
/-- Restrict the descended cell and contract the chart's *actual* unit.
This is a triangle/naturality calculation, not proof irrelevance. -/
theorem restrictUndo (N : C ≌ D) (F : D ⥤ R) (G : C ⥤ R) (q : N.functor ⋙ F ≅ G) :
    whiskerLeft N.functor (undoChart N F G q).hom ≫ whiskerRight N.unitIso.inv G = q.hom := by
  ext x
  change (F.map (N.counitIso.inv.app (N.functor.obj x)) ≫ q.hom.app (N.inverse.obj (N.functor.obj x))) ≫ G.map (N.unitIso.inv.app x) = q.hom.app x
  rw [Category.assoc, ← q.hom.naturality]
  simp only [Functor.comp_map, ← Category.assoc, ← F.map_comp]
  rw [show N.counitIso.inv.app (N.functor.obj x) ≫ N.functor.map (N.unitIso.inv.app x) = 𝟙 _ from N.counitInv_functor_comp x]
  simp
theorem restrictInjective (N : C ≌ D) (F G : D ⥤ R) :
    Function.Injective (fun a : F ⟶ G => whiskerLeft N.functor a) := by
  intro a b same
  ext x
  let i := N.counitIso.app x
  have h := NatTrans.congr_app same (N.inverse.obj x)
  change a.app (N.functor.obj (N.inverse.obj x)) = b.app _ at h
  apply (cancel_epi (F.map i.hom)).mp
  exact (a.naturality i.hom).trans ((congrArg (· ≫ G.map i.hom) h).trans (b.naturality i.hom).symm)
theorem cancelTransport (N : C ≌ D) (F : D ⥤ R) (G : C ⥤ R) (a b : F ⟶ N.inverse ⋙ G)
    (h : whiskerLeft N.functor a ≫ whiskerRight N.unitIso.inv G =
      whiskerLeft N.functor b ≫ whiskerRight N.unitIso.inv G) : a = b :=
  restrictInjective N F _ ((cancel_mono (isoWhiskerRight N.unitIso.symm G).hom).mp h)
end General
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : Psh.{u,max u v,u,v} B) (A : B)
noncomputable abbrev fixedCells : ZeroPower.Sum.map (first S Y A) ≅ ZeroPower.Sum.map (second S Y A) :=
  Sigma.natIso fun i => isoWhiskerRight (eqToIso (BlockCompositor.fixedCompositor S Y A i.1 i.2))
    (Sigma.incl (C := double S Y A) i)
noncomputable abbrev route :=
  chartEq S Y A ≪≫ isoWhiskerRight (fixedCells S Y A) (packing S Y A).functor ≪≫ eqToIso (oldChart S Y A)
/- The restriction of the published binary compositor is prescribed,
including both the native and the packing charts. -/
set_option maxHeartbeats 1200000 in
theorem restrictCompositor :
    whiskerLeft (nativeEquiv S Y A).functor (BlockCompositor.compositor S Y A).hom ≫
      whiskerRight (nativeEquiv S Y A).unitIso.inv (packedEquiv S Y A).functor =
      (route S Y A).hom :=
  restrictUndo (nativeEquiv S Y A) (stages S Y A) (packedEquiv S Y A).functor (route S Y A)
set_option maxHeartbeats 1000000 in
theorem unique (a : stages S Y A ⟶ previous S Y A)
    (h : whiskerLeft (nativeEquiv S Y A).functor a ≫
      whiskerRight (nativeEquiv S Y A).unitIso.inv (packedEquiv S Y A).functor = (route S Y A).hom) :
    a = (BlockCompositor.compositor S Y A).hom :=
  cancelTransport (nativeEquiv S Y A) (stages S Y A) (packedEquiv S Y A).functor a
    (BlockCompositor.compositor S Y A).hom (h.trans (restrictCompositor S Y A).symm)
set_option maxHeartbeats 1200000 in
theorem atCut (i : Nat × Nat) (x : coords S Y A i) :
    (BlockCompositor.compositor S Y A).hom.app ((nativeEquiv S Y A).functor.obj ⟨i,x⟩) ≫
      (packedEquiv S Y A).functor.map ((nativeEquiv S Y A).unitIso.inv.app ⟨i,x⟩) =
    (chartEq S Y A).hom.app ⟨i,x⟩ ≫
      (packing S Y A).functor.map ((Sigma.incl (C := double S Y A) i).map
        ((eqToHom (BlockCompositor.fixedCompositor S Y A i.1 i.2)).app x)) ≫
      (eqToHom (oldChart S Y A)).app ⟨i,x⟩ := by
  exact NatTrans.congr_app (restrictCompositor S Y A) ⟨i,x⟩
end ContextualComposition.GrothendieckStep.ChartRestriction
