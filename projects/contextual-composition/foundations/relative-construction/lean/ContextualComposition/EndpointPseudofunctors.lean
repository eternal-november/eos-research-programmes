module
public import ContextualComposition.EndpointBicategory
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint.Presentation
open CategoryTheory CategoryTheory.Functor
open scoped CategoryTheory.Bicategory
universe vK vL vC uK uL uC
variable (C : Type uC) [Category.{vC} C]
set_option backward.isDefEq.respectTransparency false

private theorem reverseUnit {A : Type*} [Category* A] {w x y z : A} (i : w ≅ x) (j : x ≅ z)
    (k : w ≅ y) (l : y ≅ z) (eq : i.hom ≫ j.hom = k.hom ≫ l.hom) :
    l.inv = j.inv ≫ i.inv ≫ k.hom := by
  have h : i ≪≫ j = k ≪≫ l := Iso.ext eq
  have hi := congrArg (fun (m : w ≅ z) => m.inv ≫ k.hom) h
  simpa only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hi.symm

private theorem choiceReverse {A A' : (Presentation.{vK,vL,vC,uK,uL,uC} C)} {T U : A ⟶ A'} (η : T ⟶ U) :
    (localizedChoiceIso (ChoiceIso.symm η)).hom = (localizedChoiceIso η).inv := by
  apply (cancel_mono (localizedChoiceIso η).hom).mp
  rw [Iso.inv_hom_id, ← localized_choice_composition]
  have h : (ChoiceIso.symm η).trans η = ChoiceIso.refl U :=
    @Groupoid.inv_comp (Data A.source A.target A'.source A'.target) dataGroupoid T U η
  rw [h, localized_choice_identity]

/-- Lax direction of the localization transport before displaying its invertible comparison cells. -/
noncomputable def localizedLax : (Presentation.{vK,vL,vC,uK,uL,uC} C) ⥤ᴸ Cat where
  obj A := Cat.of (Primitive.generators A.source A.target).Localization
  map T := (localizedFactorFunctor T).toCatHom
  map₂ η := (localizedChoiceIso η).hom.toCatHom₂
  map₂_id T := congrArg NatTrans.toCatHom₂ (localized_choice_identity T)
  map₂_comp η θ := congrArg NatTrans.toCatHom₂ (localized_choice_composition η θ)
  mapId A := (localizedIdentityIso (e := A.source) (d := A.target)).inv.toCatHom₂
  mapComp T U := (localizedCompositionIso T U).hom.toCatHom₂
  mapComp_naturality_left η T := congrArg NatTrans.toCatHom₂ (localized_composition_right_naturality η T)
  mapComp_naturality_right := by intros; apply Cat.Hom₂.ext; apply localized_composition_left_naturality
  map₂_associator T U V := congrArg NatTrans.toCatHom₂ (localized_associativity T U V)
  map₂_leftUnitor T := by
    apply Cat.Hom₂.ext
    change (localizedChoiceIso (leftUnitChoice T).symm).hom = _
    rw [choiceReverse C (η := leftUnitChoice T)]
    exact reverseUnit (isoWhiskerRight localizedIdentityIso _) (Functor.leftUnitor _) (localizedCompositionIso _ _) _ (localized_left_unit T)
  map₂_rightUnitor T := by
    apply Cat.Hom₂.ext
    change (localizedChoiceIso (rightUnitChoice T).symm).hom = _
    rw [choiceReverse C (η := rightUnitChoice T)]
    exact reverseUnit (isoWhiskerLeft _ localizedIdentityIso) (Functor.rightUnitor _) (localizedCompositionIso _ _) _ (localized_right_unit T)

noncomputable def localizedPseudo : (Presentation.{vK,vL,vC,uK,uL,uC} C) ⥤ᵖ Cat := Pseudofunctor.mkOfLax (localizedLax C)
  { mapIdIso := fun A => Cat.Hom.isoMk (localizedIdentityIso (e := A.source) (d := A.target))
    mapCompIso := fun T U => Cat.Hom.isoMk (localizedCompositionIso T U).symm }

local macro "comma_ext" : tactic =>
  `(tactic| (apply Cat.Hom₂.ext; apply NatTrans.ext; funext s; apply Comma.hom_ext))

/-- Comma transport uses native grade maps and their original lift squares. -/
def commaLax : (Presentation.{vK,vL,vC,uK,uL,uC} C) ⥤ᴸ Cat where
  obj A := Cat.of (Comma A.source A.target)
  map T := (commaFunctor T).toCatHom
  map₂ η := (ChoiceIso.commaIso η).hom.toCatHom₂
  map₂_id T := by comma_ext <;> rfl
  map₂_comp η θ := congrArg NatTrans.toCatHom₂ (ChoiceIso.comma_trans η θ)
  mapId A := (commaIdentityIso (e := A.source) (d := A.target)).inv.toCatHom₂
  mapComp T U := (commaCompositionIso T U).hom.toCatHom₂
  mapComp_naturality_left η T := by
    comma_ext <;> change 𝟙 _ ≫ _ = _ ≫ 𝟙 _ <;> erw [Category.id_comp, Category.comp_id] <;> rfl
  mapComp_naturality_right := by
    intros; comma_ext <;> change 𝟙 _ ≫ _ = _ ≫ 𝟙 _ <;> erw [Category.id_comp, Category.comp_id] <;> rfl
  map₂_associator T U V := by
    comma_ext
    · change V.input.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
      rw [Functor.map_id]
    · change V.output.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
      rw [Functor.map_id]
  map₂_leftUnitor T := by
    comma_ext
    · change 𝟙 _ = 𝟙 _ ≫ T.input.map (𝟙 _) ≫ 𝟙 _; rw [Functor.map_id]; simp
    · change 𝟙 _ = 𝟙 _ ≫ T.output.map (𝟙 _) ≫ 𝟙 _; rw [Functor.map_id]; simp
  map₂_rightUnitor T := by comma_ext <;> change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ <;> simp

def commaPseudo : (Presentation.{vK,vL,vC,uK,uL,uC} C) ⥤ᵖ Cat := Pseudofunctor.mkOfLax (commaLax C)
  { mapIdIso := fun A => Cat.Hom.isoMk (commaIdentityIso (e := A.source) (d := A.target))
    mapCompIso := fun T U => Cat.Hom.isoMk (commaCompositionIso T U).symm }

end ContextualComposition.Factorization.Endpoint.Presentation
