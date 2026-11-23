module
public import ContextualComposition.EndpointGrothendieck
public import ContextualComposition.EndpointEquivalence
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint.Indexed
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory Opposite
open scoped CategoryTheory.Bicategory
universe vK vL vC uK uL uC
variable {C : Type uC} [Category.{vC} C]
variable (K : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vK,uK}) (L : LocallyDiscrete C ⥤ᵖ Cat.{vL,uL})
variable (e : Pseudofunctor.CoGrothendieck K ⥤ C) (d : Pseudofunctor.Grothendieck L ⥤ C)
set_option backward.isDefEq.respectTransparency false

private theorem choiceInputEq {A B : Presentation.{vK,vL,vC,uK,uL,uC} C} {f g : A ⟶ B} (h : f = g)
    (x : A.input) :
    (ChoiceIso.input (eqToHom h : f ⟶ g)).hom.app x = eqToHom (by subst h; rfl) := by subst h; rfl
private theorem choiceOutputEq {A B : Presentation.{vK,vL,vC,uK,uL,uC} C} {f g : A ⟶ B} (h : f = g)
    (x : A.output) :
    (ChoiceIso.output (eqToHom h : f ⟶ g)).hom.app x = eqToHom (by subst h; rfl) := by subst h; rfl

/-- The source-indexed transport pseudofunctor, built from the actual extension functors on both Grothendieck total categories. -/
def action : LocallyDiscrete (Cᵒᵖ × C) ⥤ᵖ Presentation.{vK,vL,vC,uK,uL,uC} C :=
  LocallyDiscrete.mkPseudofunctor (presentation K L e d) (transport K L e d)
    (fun i => Presentation.choiceToIso (identityChoice K L e d i))
    (fun p q => Presentation.choiceToIso (compositionChoice K L e d p q))
    (by
      intro i j k l p q r
      apply ChoiceIso.ext <;> apply Iso.ext <;> apply NatTrans.ext <;> funext x
      · rw [choiceInputEq]
        have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (K.map₂_associator p.1.toLoc q.1.toLoc r.1.toLoc)) x
        simp only [Strict.associator_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app] at h
        exact h.symm
      · rw [choiceOutputEq]
        have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (L.map₂_associator p.2.toLoc q.2.toLoc r.2.toLoc)) x
        simp only [Strict.associator_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app] at h
        exact h.symm)
    (by
      intro i j p
      apply ChoiceIso.ext <;> apply Iso.ext <;> apply NatTrans.ext <;> funext x
      · rw [choiceInputEq]
        have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (K.map₂_left_unitor p.1.toLoc)) x
        simp only [Strict.leftUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app] at h
        exact h.symm
      · rw [choiceOutputEq]
        have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (L.map₂_left_unitor p.2.toLoc)) x
        simp only [Strict.leftUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app] at h
        exact h.symm)
    (by
      intro i j p
      apply ChoiceIso.ext <;> apply Iso.ext <;> apply NatTrans.ext <;> funext x
      · rw [choiceInputEq]
        have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (K.map₂_right_unitor p.1.toLoc)) x
        simp only [Strict.rightUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app] at h
        exact h.symm
      · rw [choiceOutputEq]
        have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (L.map₂_right_unitor p.2.toLoc)) x
        simp only [Strict.rightUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app] at h
        exact h.symm)

end ContextualComposition.Factorization.Endpoint.Indexed
