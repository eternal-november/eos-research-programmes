module
public import ContextualComposition.EndpointNormalization
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint.Presentation
open CategoryTheory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vK vL vC uK uL uC
variable (C : Type uC) [Category.{vC} C]

private theorem unitPastings {D : Type*} [Category* D] {a b c d : D}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : a ⟶ d) (e : f ≫ g ≫ h = k) :
    f ≫ 𝟙 _ ≫ g ≫ 𝟙 _ ≫ h ≫ 𝟙 _ = (𝟙 _ ≫ 𝟙 _) ≫ k := by simpa using e

private theorem counitPastings {D : Type*} [Category* D] {a b c d : D}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : a ⟶ d) (e : f ≫ g ≫ h = k) :
    k ≫ (𝟙 _ ≫ 𝟙 _) = (𝟙 _ ≫ f ≫ 𝟙 _ ≫ g ≫ 𝟙 _) ≫ h := by simpa [Category.assoc] using e.symm

private theorem trianglePasting {D : Type*} [Category* D] {a b : D} (f : a ⟶ b) (g : b ⟶ a)
    (h : f ≫ g = 𝟙 a) : f ≫ 𝟙 _ ≫ g = 𝟙 _ ≫ 𝟙 a := by simpa using h

private theorem triangleShape {D : Type*} [Bicategory D] {A B : D} {f : A ⟶ B} {g : B ⟶ A}
    (η : 𝟙 A ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 B) :
    (Bicategory.leftZigzagIso η ε).hom = η.hom ▷ f ≫ (α_ f g f).hom ≫ f ◁ ε.hom := by
  dsimp only [Bicategory.leftZigzagIso, bicategoricalIsoComp, Iso.trans_hom]
  congr 1
  congr 1
  bicategory_coherence

/-- The unit modification uses the adjusted unit of the actual localization equivalence. -/
noncomputable def normalizationUnit : 𝟙 (largeLocalization.{vK,vL,vC,uK,uL,uC} C) ≅ normalization C ≫ sectionTransformation C :=
  Pseudofunctor.StrongTrans.isoMk (fun A => Cat.Hom.isoMk (UniverseLift.iso (Primitive.localizationEquivalence A.source A.target).unitIso)) (by
    intro A B T
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext s; apply ULift.ext
    have h := packaged_unit_compatibility T (ULift.down s)
    exact unitPastings _ _ _ _ h)

/-- The counit modification uses the counit of the same equivalence in every fibre. -/
noncomputable def normalizationCounit : sectionTransformation C ≫ normalization C ≅ 𝟙 (largeComma.{vK,vL,vC,uK,uL,uC} C) :=
  Pseudofunctor.StrongTrans.isoMk (fun A => Cat.Hom.isoMk (UniverseLift.iso (Primitive.localizationEquivalence A.source A.target).counitIso)) (by
    intro A B T
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext s; apply ULift.ext
    have h := packaged_counit_compatibility T (ULift.down s)
    exact counitPastings _ _ _ _ h)

/-- Normalization is an adjoint equivalence of Cat-valued pseudofunctors on the full endpoint transport bicategory at the chosen universes. -/
noncomputable def normalizationEquivalence :
    Bicategory.Equivalence (largeLocalization.{vK,vL,vC,uK,uL,uC} C) (largeComma C) where
  hom := normalization C
  inv := sectionTransformation C
  unit := normalizationUnit C
  counit := normalizationCounit C
  left_triangle := by
    apply Iso.ext
    rw [triangleShape]
    apply Pseudofunctor.StrongTrans.Hom.ext
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext A
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext s; apply ULift.ext
    have h := (Primitive.localizationEquivalence A.source A.target).functor_unitIso_comp (ULift.down s)
    exact trianglePasting _ _ h

end ContextualComposition.Factorization.Endpoint.Presentation
