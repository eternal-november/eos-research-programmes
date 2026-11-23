module
public import ContextualComposition.RelativeTensorLeftUnitChange
public import ContextualComposition.RelativeTensorFactorComposition
public import ContextualComposition.PointwisePseudonaturalEquivalence

@[expose] public section
namespace ContextualComposition.RelativeTensor.LeftUnit
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u vG uG
variable {B : Type u} [Category.{v} B]

section Diagram
variable (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG})

/-- The relative tensor of the discrete hom and a weak contravariant factor as the input endpoint varies. -/
def endpointFunctor : Bᵒᵖ ⥤ Cat where
  obj a := Cat.of (Tensor (represented a.unop) G)
  map f := (mapFirst (G := G) (precompose f.unop)).toCatHom
  map_id a := congrArg Functor.toCatHom ((congrArg (fun k => mapFirst (G := G) k) (precompose_id a.unop)).trans First.map_identity)
  map_comp f g := congrArg Functor.toCatHom ((congrArg (fun k => mapFirst (G := G) k) (precompose_comp g.unop f.unop)).trans (First.map_composite _ _))

end Diagram

section Indexed
variable (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vG uG,max u v uG})

/-- Evaluation is pseudonatural at every outer endpoint; its squares keep the nontrivial compositors of the supplied action. -/
def indexedEvaluation : (endpointFunctor G).toPseudofunctor' ⟶ G where
  app a := (evaluation a.as.unop G).toCatHom
  naturality f := Cat.Hom.isoMk (baseChange f.as.unop G)
  naturality_naturality {a b f g} m := by
    obtain rfl := LocallyDiscrete.eq_of_hom m
    obtain rfl := Subsingleton.elim m (𝟙 f)
    rw [PrelaxFunctor.map₂_id,PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (evaluation b.as.unop G).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [Functor.map_id,Category.id_comp,Category.comp_id]
  naturality_id a := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    let p := z.as.first.as.op.toLoc
    let t := (Cat.Hom.toNatIso (G.mapId a)).app ((G.map p).toFunctor.obj z.as.second)
    have h := G.mapComp_id_right_hom_app p z.as.second
    simp only [Bicategory.Strict.rightUnitor_eqToIso,eqToIso.hom,PrelaxFunctor.map₂_eqToHom,Cat.eqToHom_app] at h
    change (G.mapComp p (𝟙 a)).hom.toNatTrans.app z.as.second ≫ t.hom =
      (evaluation a.as.unop G).map (((endpointFunctor G).toPseudofunctor'.mapId a).hom.toNatTrans.app z) ≫ 𝟙 _ ≫ 𝟙 _
    rw [h]
    change (eqToHom _ ≫ t.inv) ≫ t.hom = _
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,Functor.toPseudofunctor'_mapId,eqToIso.hom,Cat.eqToHom_app,eqToHom_map]
  naturality_comp {a b c} f g := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    let p := z.as.first.as.op.toLoc
    have h := G.mapComp_assoc_right_hom_app p f g z.as.second
    simp only [Bicategory.Strict.associator_eqToIso,eqToIso.inv,PrelaxFunctor.map₂_eqToHom,Cat.eqToHom_app] at h
    change (G.mapComp p (f ≫ g)).hom.toNatTrans.app z.as.second ≫ (G.mapComp f g).hom.toNatTrans.app ((G.map p).toFunctor.obj z.as.second) =
      (evaluation c.as.unop G).map (((endpointFunctor G).toPseudofunctor'.mapComp f g).hom.toNatTrans.app z) ≫
      𝟙 _ ≫ (G.mapComp (p ≫ f) g).hom.toNatTrans.app z.as.second ≫ 𝟙 _ ≫
      (G.map g).toFunctor.map ((G.mapComp p f).hom.toNatTrans.app z.as.second) ≫ 𝟙 _
    simp only [Functor.toPseudofunctor'_mapComp,eqToIso.hom,Cat.eqToHom_app,eqToHom_map,Category.id_comp,Category.comp_id]
    exact h

theorem indexedEvaluation_component (a : LocallyDiscrete Bᵒᵖ) : ((indexedEvaluation.{v,u,vG,uG} G).app a).toFunctor = evaluation a.as.unop G := rfl

theorem indexedEvaluation_square {a b : LocallyDiscrete Bᵒᵖ} (f : a ⟶ b) :
    Cat.Hom.toNatIso ((indexedEvaluation.{v,u,vG,uG} G).naturality f) = baseChange f.as.unop G := rfl

/-- The indexed left unitor at common Cat universes, with the given evaluation as its forward strong transformation. -/
noncomputable def indexedEquivalence : Bicategory.Equivalence (endpointFunctor G).toPseudofunctor' G := by
  letI : ∀ a, ((indexedEvaluation.{v,u,vG,uG} G).app a).toFunctor.IsEquivalence := fun a => (equivalence a.as.unop G).isEquivalence_functor
  exact PseudonaturalInverse.equivalence (indexedEvaluation.{v,u,vG,uG} G)

end Indexed
end ContextualComposition.RelativeTensor.LeftUnit
