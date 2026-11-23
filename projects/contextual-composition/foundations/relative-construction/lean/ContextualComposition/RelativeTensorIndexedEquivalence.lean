module
public import ContextualComposition.RelativeTensorIndexedComma
public import ContextualComposition.PointwisePseudonaturalEquivalence

@[expose] public section
namespace ContextualComposition.RelativeTensor.Presented
open CategoryTheory Opposite Factorization
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vK vL vC uK uL uC
variable {C : Type uC} [Category.{vC} C]
set_option backward.isDefEq.respectTransparency false

/-- The explicitly constructed fibre equivalence after raising both category universes. Its forward map is the displayed normalization component. -/
noncomputable def liftedFibre (A : Endpoint.Presentation.{vK,vL,vC,uK,uL,uC} C) :
    CategoryTheory.Equivalence ((largeTensor C).obj A) ((Endpoint.Presentation.largeComma C).obj A) :=
  (AsSmall.equiv (C := Carrier A.source A.target)).symm.trans
    ((equivalence A.source A.target).trans (AsSmall.equiv (C := Comma A.source A.target)))

theorem component_functor (A : Endpoint.Presentation.{vK,vL,vC,uK,uL,uC} C) :
    ((normalization C).app A).toFunctor = (liftedFibre A).functor := rfl

/-- The strictness of the comma indexing functors in their common middle variable imposes no strictness on endpoint transport. -/
noncomputable def globalEquivalence (C : Type uC) [Category.{vC} C] :
    Bicategory.Equivalence (largeTensor.{vK,vL,vC,uK,uL,uC} C) (Endpoint.Presentation.largeComma C) := by
  letI : ∀ A, ((normalization.{vK,vL,vC,uK,uL,uC} C).app A).toFunctor.IsEquivalence := fun A =>
    (liftedFibre A).isEquivalence_functor
  exact PseudonaturalInverse.equivalence (normalization C)

/-- The actual Cᵒᵖ × C tensor of the two presented modules normalizes pseudonaturally to the native comma action. -/
noncomputable def sourceEquivalence
    (K : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vK,uK}) (L : LocallyDiscrete C ⥤ᵖ Cat.{vL,uL})
    (e : Pseudofunctor.CoGrothendieck K ⥤ C) (d : Pseudofunctor.Grothendieck L ⥤ C) :
    Bicategory.Equivalence ((Endpoint.Indexed.action K L e d).comp (largeTensor C))
      ((Endpoint.Indexed.action K L e d).comp (Endpoint.Presentation.largeComma C)) :=
  Endpoint.Indexed.reindexEquivalence (Endpoint.Indexed.action K L e d) (globalEquivalence C)

end ContextualComposition.RelativeTensor.Presented
