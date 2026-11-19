module
public import ContextualComposition.ContextadCoherence
@[expose] public section
namespace ContextualComposition.GrothendieckStep.WeightedCells
open CategoryTheory CategoryTheory.Functor Opposite FibreValue
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B K L : Type*} [Category* B] [Category* K] [Category* L]
variable (Y : Bᵒᵖ ⥤ Cat.{v,u}) (e : K ⥤ B) (d : L ⥤ B)
variable {r s : K ⥤ L} {l : r ⋙ d ⟶ e} {m : s ⋙ d ⟶ e}
variable (i : r ≅ s) (h : whiskerRight i.hom d ≫ m = l)
include h in
theorem cellComm :
    restrictionCell Y e d s m ≫ whiskerRight (NatIso.op i).hom (diagram Y d) =
      restrictionCell Y e d r l := by
  apply NatTrans.ext
  funext x
  change (Y ⋙ Cat.opFunctor).map (m.app x.unop).op ≫
      (Y ⋙ Cat.opFunctor).map (d.map (i.hom.app x.unop)).op = (Y ⋙ Cat.opFunctor).map (l.app x.unop).op
  rw [← Functor.map_comp,← op_comp]
  exact congrArg (fun f => (Y ⋙ Cat.opFunctor).map f.op) (NatTrans.congr_app h x.unop)
def preWeighted : Grothendieck.map (restrictionCell Y e d s m) ⋙ Grothendieck.pre (diagram Y d) s.op ≅
    Grothendieck.map (restrictionCell Y e d r l) ⋙ Grothendieck.pre (diagram Y d) r.op :=
  isoWhiskerLeft (Grothendieck.map (restrictionCell Y e d s m)) (Grothendieck.preNatIso (diagram Y d) (NatIso.op i)) ≪≫
    eqToIso (congrArg (· ⋙ Grothendieck.pre (diagram Y d) r.op)
      ((Grothendieck.map_comp_eq _ _).symm.trans (congrArg Grothendieck.map (cellComm Y e d i h))))
/-- The input is a native grade isomorphism and its endpoint equation.
Neither endpoint comparison needs to be invertible. -/
def weightIso : restrict Y e d r l ≅ restrict Y e d s m := NatIso.op (preWeighted Y e d i h)
theorem weightGrade (x : Total Y e) :
    gradeMap ((weightIso Y e d i h).hom.app x) = i.hom.app (grade Y e x) := by
  apply Quiver.Hom.op_inj
  change ((preWeighted Y e d i h).hom.app x.unop).base = _
  unfold preWeighted
  simp only [Iso.trans_hom,NatTrans.comp_app,isoWhiskerLeft_hom,whiskerLeft_app,eqToIso.hom]
  rw [Grothendieck.comp_base]
  have hE : (eqToHom (Functor.congr_obj (congrArg (· ⋙ Grothendieck.pre (diagram Y d) r.op)
      ((Grothendieck.map_comp_eq _ _).symm.trans (congrArg Grothendieck.map (cellComm Y e d i h)))) x.unop) : ((Grothendieck.map (restrictionCell Y e d s m) ⋙
      (Grothendieck.map (whiskerRight (NatIso.op i).hom (diagram Y d)) ⋙ Grothendieck.pre (diagram Y d) r.op)).obj x.unop) ⟶
      ((Grothendieck.map (restrictionCell Y e d r l) ⋙ Grothendieck.pre (diagram Y d) r.op).obj x.unop)).base = 𝟙 _ := by
    rw [Grothendieck.base_eqToHom]; rfl
  rw [eqToHom_app,hE,Category.comp_id]
  rfl
theorem rawPureComp {C : Type*} [Category* C] {T : C ⥤ Cat.{v,u}}
    {x y z : Grothendieck T} {f : x ⟶ y} {g : y ⟶ z}
    (h : Pure f.fiber) (k : Pure g.fiber) : Pure (f ≫ g).fiber := by
  rw [Grothendieck.comp_fiber]
  exact pureComp ⟨_,rfl⟩ (pureComp (pureMap _ h) k)
theorem rawPureCast {C : Type*} [Category* C] {T : C ⥤ Cat.{v,u}}
    {x y : Grothendieck T} (h : x = y) : Pure (Grothendieck.Hom.fiber (eqToHom h)) :=
  ⟨_,Grothendieck.fiber_eqToHom h⟩
theorem pureUnop {C : Type*} [Category* C] {x y : Cᵒᵖ} {f : x ⟶ y}
    (h : Pure f) : Pure f.unop := by
  obtain ⟨e,rfl⟩ := h
  exact ⟨_,eqToHom_unop e⟩
theorem weightPayloadPure (x : Total Y e) :
    Pure (payloadMap ((weightIso Y e d i h).hom.app x)) := by
  change Pure ((Grothendieck.Hom.fiber ((preWeighted Y e d i h).hom.app x.unop)).unop)
  apply pureUnop
  unfold preWeighted
  simp only [Iso.trans_hom,NatTrans.comp_app,isoWhiskerLeft_hom,whiskerLeft_app,eqToIso.hom]
  rw [eqToHom_app]
  apply rawPureComp
  · exact pureId _
  · exact rawPureCast _

/-- Grade and payload test on actual arrows: pure payloads are uniquely determined
after the grade component is fixed. -/
theorem pureArrowEq {x y : Total Y d} {a b : x ⟶ y} (e : gradeMap a = gradeMap b)
    (ha : Pure (payloadMap a)) (hb : Pure (payloadMap b)) : a = b := by
  apply (homEquiv _ _).injective
  have aux (g h : grade Y d x ⟶ grade Y d y) (k : g = h)
      (f : payload Y d x ⟶ (Y.map (d.map g).op).toFunctor.obj (payload Y d y))
      (j : payload Y d x ⟶ (Y.map (d.map h).op).toFunctor.obj (payload Y d y))
      (hf : Pure f) (hj : Pure j) : HEq f j := by
    subst h
    exact heq_of_eq (pureEq hf hj)
  exact Sigma.ext e (aux _ _ e _ _ ha hb)
theorem totalPureComp {x y z : Total Y d} {f : x ⟶ y} {g : y ⟶ z}
    (hf : Pure (payloadMap f)) (hg : Pure (payloadMap g)) : Pure (payloadMap (f ≫ g)) := by
  rw [payload_comp]
  exact pureComp hf (pureComp (pureMap _ hg) ⟨_,rfl⟩)
theorem totalPureId (x : Total Y d) : Pure (payloadMap (𝟙 x)) := by
  change Pure (Grothendieck.Hom.fiber (𝟙 x.unop)).unop
  rw [Grothendieck.id_fiber]
  exact pureUnop ⟨_,rfl⟩
theorem weightId (c : whiskerRight (Iso.refl r).hom d ≫ l = l) :
    (weightIso Y e d (Iso.refl r) c).hom = 𝟙 _ := by
  ext x : 2
  apply pureArrowEq Y d
  · exact weightGrade Y e d (Iso.refl r) c x
  · exact weightPayloadPure Y e d _ _ _
  · exact totalPureId Y d _
theorem weightComp {t : K ⥤ L} {n : t ⋙ d ⟶ e}
    (j : s ≅ t) (k : whiskerRight j.hom d ≫ n = m)
    (c : whiskerRight (i ≪≫ j).hom d ≫ n = l) :
    (weightIso Y e d (i ≪≫ j) c).hom =
      (weightIso Y e d i h).hom ≫ (weightIso Y e d j k).hom := by
  ext x : 2
  change _ = (weightIso Y e d i h).hom.app x ≫ (weightIso Y e d j k).hom.app x
  apply pureArrowEq Y d
  · rw [grade_comp,weightGrade,weightGrade,weightGrade]; rfl
  · exact weightPayloadPure Y e d _ _ _
  · exact totalPureComp Y d (weightPayloadPure Y e d _ _ _) (weightPayloadPure Y e d _ _ _)
end ContextualComposition.GrothendieckStep.WeightedCells
