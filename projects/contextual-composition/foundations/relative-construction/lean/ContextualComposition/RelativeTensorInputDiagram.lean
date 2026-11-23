module
public import ContextualComposition.RelativeTensorCommaTransport
public import ContextualComposition.EndpointBicategory

@[expose] public section
namespace ContextualComposition.RelativeTensor.Presented.Input
open CategoryTheory Opposite Factorization Endpoint
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vK vL vC uK uL uC
variable {C : Type uC} [Category.{vC} C]
variable {A B D : Presentation.{vK,vL,vC,uK,uL,uC} C}
set_option backward.isDefEq.respectTransparency false

def arrow (T : A ⟶ B) : input A.source ⟶ input B.source := inputComparison T

def choiceAt {T U : A ⟶ B} (m : T ⟶ U) (i : C) : inputAt T i ⟶ inputAt U i where
  app x := CostructuredArrow.homMk (m.input.hom.app x.left) (by
    change B.source.map (m.input.hom.app x.left) ≫ U.inputLift.app x.left ≫ x.hom = _
    erw [← Category.assoc,m.input_lift]; rfl)
  naturality _ _ f := CostructuredArrow.hom_ext _ _ (m.input.hom.naturality f.left)

def choice {T U : A ⟶ B} (m : T ⟶ U) : arrow T ⟶ arrow U where
  as := {
    app i := (choiceAt m i.as).toCatHom₂
    naturality := by
      intro i j f
      apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply CostructuredArrow.hom_ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm }

def identityAt (A : Presentation.{vK,vL,vC,uK,uL,uC} C) (i : C) :
    inputAt (identityData A.source A.target) i ≅ 𝟭 (CostructuredArrow A.source i) :=
  NatIso.ofComponents (fun x => CostructuredArrow.isoMk (Iso.refl x.left) (by
    change A.source.map (𝟙 _) ≫ x.hom = 𝟙 _ ≫ x.hom; rw [Functor.map_id])) (by
    intro x y f; apply CostructuredArrow.hom_ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

def compositionAt (T : A ⟶ B) (U : B ⟶ D) (i : C) :
    inputAt (composeData T U) i ≅ inputAt T i ⋙ inputAt U i :=
  NatIso.ofComponents (fun x => CostructuredArrow.isoMk (Iso.refl (U.input.obj (T.input.obj x.left))) (by
    change D.source.map (𝟙 _) ≫ U.inputLift.app _ ≫ T.inputLift.app _ ≫ x.hom =
      (𝟙 _ ≫ U.inputLift.app _ ≫ T.inputLift.app _) ≫ x.hom
    simp [Category.assoc])) (by
    intro x y f; apply CostructuredArrow.hom_ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

def identity (A : Presentation.{vK,vL,vC,uK,uL,uC} C) : arrow (𝟙 A) ≅ (𝟙 (input A.source)) :=
  Pseudofunctor.StrongTrans.isoMk (fun i => Cat.Hom.isoMk (identityAt A i.as)) (by
    intro i j f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply CostructuredArrow.hom_ext
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp)

def composition (T : A ⟶ B) (U : B ⟶ D) : arrow (T ≫ U) ≅ arrow T ≫ arrow U :=
  Pseudofunctor.StrongTrans.isoMk (fun i => Cat.Hom.isoMk (compositionAt T U i.as)) (by
    intro i j f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply CostructuredArrow.hom_ext
    change 𝟙 _ ≫ 𝟙 _ ≫ U.input.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp)

local macro "grade_ext" : tactic =>
  `(tactic| (apply Pseudofunctor.StrongTrans.homCategory.ext; intro i; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply CostructuredArrow.hom_ext))

def diagram (C : Type uC) [Category.{vC} C] : Pseudofunctor (Presentation.{vK,vL,vC,uK,uL,uC} C) (LocallyDiscrete C ⥤ᵖ Cat) where
  obj A := input A.source
  map T := arrow T
  map₂ := choice
  mapId := identity
  mapComp := composition
  map₂_id _ := by grade_ext; rfl
  map₂_comp _ _ := by grade_ext; rfl
  map₂_whisker_left := by
    intros; grade_ext; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; erw [Category.id_comp,Category.comp_id]; rfl
  map₂_whisker_right := by
    intros; grade_ext; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; erw [Category.id_comp,Category.comp_id]; rfl
  map₂_associator T U V := by
    grade_ext; change 𝟙 _ = 𝟙 _ ≫ V.input.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    rw [Functor.map_id]; simp
  map₂_left_unitor T := by
    grade_ext; change 𝟙 _ = 𝟙 _ ≫ T.input.map (𝟙 _) ≫ 𝟙 _
    simp
  map₂_right_unitor T := by
    grade_ext; change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp

end ContextualComposition.RelativeTensor.Presented.Input
