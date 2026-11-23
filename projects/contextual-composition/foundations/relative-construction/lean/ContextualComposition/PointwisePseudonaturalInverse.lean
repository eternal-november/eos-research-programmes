module
public import ContextualComposition.RecoveryTargetLaws
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

@[expose] public section
namespace ContextualComposition.PseudonaturalInverse
open CategoryTheory CategoryTheory.Functor Factorization.Endpoint
open GrothendieckStep GrothendieckStep.FibreValue
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe w v u v' u'
variable {A : Type u} [Bicategory.{w,v} A] {F G : A ⥤ᵖ Cat.{v',u'}}
variable (η : F ⟶ G) [∀ a, (η.app a).toFunctor.IsEquivalence]
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev fibre (a : A) := (η.app a).toFunctor.asEquivalence
abbrev square {a b : A} (f : a ⟶ b) := Cat.Hom.toNatIso (η.naturality f)
noncomputable abbrev mate {a b : A} (f : a ⟶ b) :=
  recoverySquare (fibre η a) (fibre η b) (F.map f).toFunctor (G.map f).toFunctor (square η f)

private theorem flip {C : Type*} [Category* C] {a b c d : C} (i : a ≅ b) (j : c ≅ d) (p : a ⟶ c) (q : b ⟶ d)
    (h : p ≫ j.hom = i.hom ≫ q) : q ≫ j.inv = i.inv ≫ p := by
  apply (cancel_epi i.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem inverse_change {a b : A} {f g : a ⟶ b} (m : f ⟶ g) (y : G.obj a) :
    (fibre η b).inverse.map ((G.map₂ m).toNatTrans.app y) ≫ (mate η g).hom.app y =
      (mate η f).hom.app y ≫ (F.map₂ m).toNatTrans.app ((fibre η a).inverse.obj y) := by
  apply recoverySquare_modification
  intro x
  exact flip ((square η f).app x) ((square η g).app x) _ _
    (NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (η.naturality_naturality m)) x)

theorem inverse_identity (a : A) (y : G.obj a) :
    (mate η (𝟙 a)).hom.app y ≫ (F.mapId a).hom.toNatTrans.app ((fibre η a).inverse.obj y) =
      (fibre η a).inverse.map ((G.mapId a).hom.toNatTrans.app y) := by
  let p := (square η (𝟙 a)).symm
  have h : Paste.UnitLaw p.symm (F.mapId a).hom.toNatTrans (G.mapId a).hom.toNatTrans := by
    intro x
    have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (η.naturality_id a)) x
    change _ = _ ≫ 𝟙 _ ≫ 𝟙 _ at h
    simp only [Category.comp_id] at h
    exact h
  have r := MateLaws.unit (fibre η a) p _ _ h y
  rw [← recovery_eq_mate] at r
  exact r

theorem inverse_composite {a b c : A} (f : a ⟶ b) (g : b ⟶ c) (y : G.obj a) :
    (mate η (f ≫ g)).hom.app y ≫ (F.mapComp f g).hom.toNatTrans.app ((fibre η a).inverse.obj y) =
      (fibre η c).inverse.map ((G.mapComp f g).hom.toNatTrans.app y) ≫
      (mate η g).hom.app ((G.map f).toFunctor.obj y) ≫ (F.map g).toFunctor.map ((mate η f).hom.app y) := by
  let u := (F.mapComp f g).hom.toNatTrans
  let v := (G.mapComp f g).hom.toNatTrans
  have h : Paste.CompLaw (square η (f ≫ g)) (square η g) (square η f) u v := by
    intro x
    have hc := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (η.naturality_comp f g)) x
    change _ = _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ at hc
    simp only [Category.id_comp, Category.comp_id] at hc
    exact hc
  have r := MateLaws.comp (fibre η c) (fibre η b) (fibre η a) (square η (f ≫ g)).symm
    (square η g).symm (square η f).symm u v h y
  simp only [← recovery_eq_mate] at r
  exact r

private theorem unitorTail {C : Type*} [Category* C] {a b c : C} (p : a ⟶ b) (q : b ⟶ c) (r : a ⟶ c)
    (h : p ≫ q = r) : p ≫ q = r ≫ 𝟙 _ ≫ 𝟙 _ := by simpa using h

/-- The adjoint mates of the given forward squares supply actual inverse strong naturality. -/
noncomputable def inverse : G ⟶ F where
  app a := (fibre η a).inverse.toCatHom
  naturality f := Cat.Hom.isoMk (mate η f)
  naturality_naturality m := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    exact inverse_change η m x
  naturality_id a := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    exact unitorTail _ _ _ (inverse_identity η a x)
  naturality_comp f g := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change _ = _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _
    erw [Category.id_comp,Category.id_comp,Category.comp_id]
    exact inverse_composite η f g x

end ContextualComposition.PseudonaturalInverse
