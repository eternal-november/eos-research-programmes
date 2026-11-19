module
public import ContextualComposition.ContextadInsideCharts
public import ContextualComposition.ContextadModification
public import ContextualComposition.ContextadPayloadModification
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadOuterCharts
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeCleavage BoundaryPaste ContextadRoutes
set_option backward.isDefEq.respectTransparency false
universe b w
section Lift
variable {B K J X : Type*} [Category* B] [Category* K] [Category* J] [Category* X]
variable (Y : Bᵒᵖ ⥤ Cat.{w,b}) (d : J ⥤ B) {e : K ⥤ J} {e' : X ⥤ J} (r : K ⥤ X)
variable (l : r ⋙ e' ⟶ e)
def liftTail :
    restrict Y (e ⋙ d) (e' ⋙ d) r (whiskerRight l d) ⋙ SpanPayload.totalMap Y e' d rfl ⟶
      SpanPayload.totalMap Y e d rfl :=
  NatTrans.op (preCell (diagram Y d) (NatTrans.op l))
theorem liftGrade (x : Total Y (e ⋙ d)) :
    gradeMap ((liftTail Y d r l).app x) = l.app (grade _ _ x) := rfl
theorem liftPayload (x : Total Y (e ⋙ d)) :
    payloadMap ((liftTail Y d r l).app x) = 𝟙 _ := rfl
theorem liftCart {D : Type*} [Category* D] (p : J ⥤ D)
    (h : ∀ z, Cartesian p (l.app z)) (x : Total Y (e ⋙ d)) :
    Cartesian (gradeProjection ⋙ p) ((liftTail Y d r l).app x) := by
  have : IsIso (payloadMap ((liftTail Y d r l).app x)) := by rw [liftPayload]; infer_instance
  exact composite (ContextadCartesian.cart_of_payload _ _ _) (h _)
end Lift
section Compare
variable {B C D : Type*} [Category* B] [Category* C] [Category* D] (p : D ⥤ B)
variable {F G H : C ⥤ D} (l : F ⟶ H) (r : G ⟶ H) (base : F ⋙ p = G ⋙ p)
variable (over : ∀ x, p.map (l.app x) = eqToHom (Functor.congr_obj base x) ≫ p.map (r.app x))
variable (hl : ∀ x, Cartesian p (l.app x)) (hr : ∀ x, Cartesian p (r.app x))
noncomputable def factor (x : C) := (hr x _ (l.app x) _ (over x)).choose
theorem factorOver (x : C) : p.map (factor p l r base over hr x) = eqToHom (Functor.congr_obj base x) :=
  (hr x _ _ _ (over x)).choose_spec.1.1
theorem factorFac (x : C) : factor p l r base over hr x ≫ r.app x = l.app x :=
  (hr x _ _ _ (over x)).choose_spec.1.2
theorem cancel {a b d : D} (f : b ⟶ d) (h : Cartesian p f) (g k : a ⟶ b)
    (w : p.map g = p.map k) (v : g ≫ f = k ≫ f) : g = k := by
  obtain ⟨_,_,uniq⟩ := h _ (k ≫ f) (p.map k) (p.map_comp _ _)
  exact (uniq _ ⟨w,v⟩).trans (uniq _ ⟨rfl,rfl⟩).symm
noncomputable def factorNat : F ⟶ G where
  app := factor p l r base over hr
  naturality x y a := by
    apply cancel p (r.app y) (hr y)
    · rw [p.map_comp,p.map_comp,factorOver,factorOver]
      simpa only [eqToHom_app,Functor.comp_map] using (eqToHom base).naturality a
    · rw [Category.assoc,factorFac,l.naturality,Category.assoc,r.naturality,← Category.assoc,factorFac]
include over in
theorem swapOver (x : C) : p.map (r.app x) = eqToHom (Functor.congr_obj base.symm x) ≫ p.map (l.app x) := by
  rw [over x,← Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]
noncomputable def compare : F ≅ G where
  hom := factorNat p l r base over hr
  inv := factorNat p r l base.symm (swapOver p l r base over) hl
  hom_inv_id := by
    ext x : 2
    apply cancel p (l.app x) (hl x)
    · simp [factorNat,p.map_comp,factorOver]
    · simp [factorNat,Category.assoc,factorFac]
  inv_hom_id := by
    ext x : 2
    apply cancel p (r.app x) (hr x)
    · simp [factorNat,p.map_comp,factorOver]
    · simp [factorNat,Category.assoc,factorFac]
end Compare
end ContextualComposition.GrothendieckStep.ContextadOuterCharts

namespace ContextualComposition.GrothendieckStep.ContextadOuterCharts
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SpanApex NativeBlocks BoundaryPaste FibreValue
universe b w
section Match
variable {B : Type b} [Category.{w} B] {K X : Type*} [Category* K] [Category* X]
variable (Y : Bᵒᵖ ⥤ Cat.{w,b}) (e : K ⥤ B) (F G : X ⥤ Total Y e)
variable (gr : F ⋙ gradeProjection = G ⋙ gradeProjection)
variable (a : F ⋙ second (projectionData Y) e ⟶ G ⋙ second (projectionData Y) e)
variable (h : ∀ x, Pure ((pr Y).map (a.app x)))
def mate : F ⋙ intoPullback (projectionData Y) e ⟶ G ⋙ intoPullback (projectionData Y) e where
  app x := ⟨(eqToHom gr).app x,a.app x,by
    change e.map ((eqToHom gr).app x) ≫ 𝟙 _ = 𝟙 _ ≫ (pr Y).map (a.app x)
    simp only [Category.comp_id,Category.id_comp]
    exact pureEq (pureMap e ⟨_,eqToHom_app gr x⟩) (h x)⟩
  naturality _ _ f := CategoricalPullback.hom_ext ((eqToHom gr).naturality f) (a.naturality f)
variable (i : F ⋙ second (projectionData Y) e ≅ G ⋙ second (projectionData Y) e)
noncomputable def mateIso (v : ∀ x, Pure ((pr Y).map (i.hom.app x))) : F ≅ G := by
  let J := (whiskeringRight X _ _).obj (intoPullback (projectionData Y) e)
  apply J.preimageIso
  exact { hom := mate Y e F G gr i.hom v
          inv := mate Y e G F gr.symm i.inv (fun x => ContextadLawTransport.pureInverse (i.app x) (v x))
          hom_inv_id := by
            apply NatTrans.ext; funext x
            apply CategoricalPullback.hom_ext
            · change (eqToHom gr).app x ≫ (eqToHom gr.symm).app x = 𝟙 _
              simp [eqToHom_app]
            · exact i.hom_inv_id_app x
          inv_hom_id := by
            apply NatTrans.ext; funext x
            apply CategoricalPullback.hom_ext
            · change (eqToHom gr.symm).app x ≫ (eqToHom gr).app x = 𝟙 _
              simp [eqToHom_app]
            · exact i.inv_hom_id_app x }
theorem mateGrade (v : ∀ x, Pure ((pr Y).map (i.hom.app x))) (x : X) :
    Pure (gradeMap ((mateIso Y e F G gr i v).hom.app x)) := by
  let J := (whiskeringRight X _ _).obj (intoPullback (projectionData Y) e)
  have z : J.map ((mateIso Y e F G gr i v).hom) = mate Y e F G gr i.hom v := J.map_preimage _
  have c := congrArg (fun f => CategoricalPullback.Hom.fst f) (NatTrans.congr_app z x)
  exact ⟨_,c.trans (eqToHom_app gr x)⟩
end Match
end ContextualComposition.GrothendieckStep.ContextadOuterCharts

