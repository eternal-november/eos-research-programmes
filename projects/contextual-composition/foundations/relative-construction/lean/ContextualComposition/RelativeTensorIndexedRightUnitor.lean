module
public import ContextualComposition.RelativeTensorRightUnitBaseChange
public import ContextualComposition.PointwisePseudonaturalEquivalence

@[expose] public section
namespace ContextualComposition.RelativeTensor.RightUnit
open CategoryTheory Opposite Iterated
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vF uF
variable {B : Type u} [Category.{v} B] (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF})
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem source_unit (a : B) (z : Tensor F (represented a)) :
    (evaluation a F).map (((leftInner F (unitModule B)).mapId ⟨a⟩).hom.toNatTrans.app z) =
      eqToHom (congrArg (fun p => (forward F p).obj z.as.first) (Category.comp_id z.as.second.as)) := by
  change (evaluation a F).map ((Second.mapCell (F := F) (unitPostcomposeId a).hom.as).app z ≫
    (Second.identityIso F (represented a)).hom.toNatTrans.app z) = _
  rw [Second.identity_hom_app]
  refine (congrArg (evaluation a F).map (Category.comp_id ((Second.mapCell (F := F) (unitPostcomposeId a).hom.as).app z))).trans ?_
  rw [Second.cell_app,eval_native]
  erw [Functor.map_id,Category.id_comp]

theorem source_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (z : Tensor F (represented a)) :
    (evaluation c F).map (((leftInner F (unitModule B)).mapComp f.toLoc g.toLoc).hom.toNatTrans.app z) =
      eqToHom (congrArg (fun p => (forward F p).obj z.as.first) (Category.assoc z.as.second.as f g).symm) := by
  change (evaluation c F).map ((Second.mapCell (F := F) (unitPostcomposeComp f g).hom.as).app z ≫
    (Second.compositeIso F (unitPostcompose f) (unitPostcompose g)).hom.toNatTrans.app z) = _
  rw [Second.composite_hom_app]
  refine (congrArg (evaluation c F).map (Category.comp_id ((Second.mapCell (F := F) (unitPostcomposeComp f g).hom.as).app z))).trans ?_
  rw [Second.cell_app,eval_native]
  erw [Functor.map_id,Category.id_comp]

private theorem cancelUnit {T : Type*} [Category* T] {a b c : T} (i : b ≅ c) (f : a ⟶ b) (e : a = c) (h : f = eqToHom e ≫ i.inv) :
    f ≫ i.hom = eqToHom e := by rw [h,Category.assoc,i.inv_hom_id,Category.comp_id]

private theorem moveCast {T : Type*} [Category* T] {a b c : T} (e : a = b) (p : a ⟶ c) (q : b ⟶ c) (h : p = eqToHom e ≫ q) :
    q = eqToHom e.symm ≫ p := by subst b; simpa using h.symm

theorem base_unit (a : B) (z : Tensor F (represented a)) :
    (indexedBase F (𝟙 a)).hom.app z ≫ (F.mapId ⟨a⟩).hom.toNatTrans.app ((evaluation a F).obj z) =
      (evaluation a F).map (((leftInner F (unitModule B)).mapId ⟨a⟩).hom.toNatTrans.app z) := by
  rw [indexedBase_app,source_unit]
  have h := F.mapComp_id_right_hom_app z.as.second.as.toLoc z.as.first
  simp only [Bicategory.Strict.rightUnitor_eqToIso,eqToIso.hom,PrelaxFunctor.map₂_eqToHom,Cat.eqToHom_app] at h
  exact cancelUnit ((Cat.Hom.toNatIso (F.mapId ⟨a⟩)).app ((forward F z.as.second.as).obj z.as.first)) _ _ h

theorem base_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (z : Tensor F (represented a)) :
    (indexedBase F (f ≫ g)).hom.app z ≫ (F.mapComp f.toLoc g.toLoc).hom.toNatTrans.app ((evaluation a F).obj z) =
      (evaluation c F).map (((leftInner F (unitModule B)).mapComp f.toLoc g.toLoc).hom.toNatTrans.app z) ≫
      (indexedBase F g).hom.app ((mapSecond (F := F) (unitPostcompose f)).obj z) ≫ (forward F g).map ((indexedBase F f).hom.app z) := by
  rw [indexedBase_app,source_comp,indexedBase_app,indexedBase_app]
  have h := F.mapComp_assoc_left_hom_app z.as.second.as.toLoc f.toLoc g.toLoc z.as.first
  simp only [Bicategory.Strict.associator_eqToIso,eqToIso.hom,PrelaxFunctor.map₂_eqToHom,Cat.eqToHom_app] at h
  exact moveCast (congrArg (fun p => (forward F p).obj z.as.first) (Category.assoc z.as.second.as f g)) _ _ h

section Indexed

variable (X : LocallyDiscrete B ⥤ᵖ Cat.{max u v uF vF,max u v uF})

/-- The right unitor acts pseudonaturally over the original covariant index, with the original weak evaluation at each object. -/
def indexed : leftInner X (unitModule B) ⟶ X where
  app a := (evaluation a.as X).toCatHom
  naturality u := Cat.Hom.isoMk (indexedBase X u.as)
  naturality_naturality {d e f g} n := by
    obtain rfl := LocallyDiscrete.eq_of_hom n
    obtain rfl := Subsingleton.elim n (𝟙 f)
    rw [PrelaxFunctor.map₂_id,PrelaxFunctor.map₂_id]
    simp
  naturality_id a := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (indexedBase X (𝟙 a.as)).hom.app z ≫ (X.mapId a).hom.toNatTrans.app ((evaluation a.as X).obj z) =
      (evaluation a.as X).map (((leftInner X (unitModule B)).mapId a).hom.toNatTrans.app z) ≫ 𝟙 _ ≫ 𝟙 _
    simpa only [Category.comp_id] using base_unit X a.as z
  naturality_comp {a b c} f g := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (indexedBase X (f.as ≫ g.as)).hom.app z ≫ (X.mapComp f g).hom.toNatTrans.app ((evaluation a.as X).obj z) =
      (evaluation c.as X).map (((leftInner X (unitModule B)).mapComp f g).hom.toNatTrans.app z) ≫ 𝟙 _ ≫
        (indexedBase X g.as).hom.app (((leftInner X (unitModule B)).map f).toFunctor.obj z) ≫ 𝟙 _ ≫
          (forward X g.as).map ((indexedBase X f.as).hom.app z) ≫ 𝟙 _
    simp only [Category.id_comp,Category.comp_id]
    exact base_comp X f.as g.as z

theorem indexed_app (a : LocallyDiscrete B) : ((indexed.{v,u,vF,uF} X).app a).toFunctor = evaluation a.as X := rfl

theorem indexed_naturality_app {a b : LocallyDiscrete B} (k : a ⟶ b) (z : Tensor X (represented a.as)) :
    ((indexed.{v,u,vF,uF} X).naturality k).hom.toNatTrans.app z =
      (X.mapComp z.as.second.as.toLoc k).hom.toNatTrans.app z.as.first := indexedBase_app X k.as z

/-- Pointwise contraction upgrades the indexed right unitor to an adjoint equivalence of action diagrams. -/
noncomputable def indexedEquivalence : Bicategory.Equivalence (leftInner X (unitModule B)) X := by
  letI (a : LocallyDiscrete B) : ((indexed.{v,u,vF,uF} X).app a).toFunctor.IsEquivalence := (equivalence a.as X).isEquivalence_functor
  exact ContextualComposition.PseudonaturalInverse.equivalence (indexed.{v,u,vF,uF} X)

end Indexed

end ContextualComposition.RelativeTensor.RightUnit
