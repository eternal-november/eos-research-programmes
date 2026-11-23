module
public import ContextualComposition.RelativeTensorCommaTransport
public import ContextualComposition.EndpointBicategory

@[expose] public section
namespace ContextualComposition.RelativeTensor.Presented.Output
open CategoryTheory Opposite Factorization Endpoint
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vK vL vC uK uL uC
variable {C : Type uC} [Category.{vC} C]
variable {A B D : Presentation.{vK,vL,vC,uK,uL,uC} C}
set_option backward.isDefEq.respectTransparency false

def arrow (T : A ⟶ B) : output A.target ⟶ output B.target := outputComparison T

def choiceAt {T U : A ⟶ B} (m : T ⟶ U) (i : C) : outputAt T i ⟶ outputAt U i where
  app x := StructuredArrow.homMk (m.output.hom.app x.right) (by
    change (x.hom ≫ T.outputLift.app x.right) ≫ B.target.map (m.output.hom.app x.right) = _
    erw [Category.assoc,m.output_lift]; rfl)
  naturality _ _ f := StructuredArrow.hom_ext _ _ (m.output.hom.naturality f.right)

def choice {T U : A ⟶ B} (m : T ⟶ U) : arrow T ⟶ arrow U where
  as := {
    app i := (choiceAt m i.as.unop).toCatHom₂
    naturality := by
      intro i j f
      apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply StructuredArrow.hom_ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm }

def identityAt (A : Presentation.{vK,vL,vC,uK,uL,uC} C) (i : C) :
    outputAt (identityData A.source A.target) i ≅ 𝟭 (StructuredArrow i A.target) :=
  NatIso.ofComponents (fun x => StructuredArrow.isoMk (Iso.refl x.right) (by
    change (x.hom ≫ 𝟙 _) ≫ A.target.map (𝟙 _) = x.hom; simp)) (by
    intro x y f; apply StructuredArrow.hom_ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

def compositionAt (T : A ⟶ B) (U : B ⟶ D) (i : C) :
    outputAt (composeData T U) i ≅ outputAt T i ⋙ outputAt U i :=
  NatIso.ofComponents (fun x => StructuredArrow.isoMk (Iso.refl (U.output.obj (T.output.obj x.right))) (by
    change (x.hom ≫ T.outputLift.app _ ≫ U.outputLift.app _ ≫ 𝟙 _) ≫ D.target.map (𝟙 _) =
      (x.hom ≫ T.outputLift.app _) ≫ U.outputLift.app _
    simp [Category.assoc])) (by
    intro x y f; apply StructuredArrow.hom_ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

def identity (A : Presentation.{vK,vL,vC,uK,uL,uC} C) : arrow (𝟙 A) ≅ (𝟙 (output A.target)) :=
  Pseudofunctor.StrongTrans.isoMk (fun i => Cat.Hom.isoMk (identityAt A i.as.unop)) (by
    intro i j f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply StructuredArrow.hom_ext
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp)

def composition (T : A ⟶ B) (U : B ⟶ D) : arrow (T ≫ U) ≅ arrow T ≫ arrow U :=
  Pseudofunctor.StrongTrans.isoMk (fun i => Cat.Hom.isoMk (compositionAt T U i.as.unop)) (by
    intro i j f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply StructuredArrow.hom_ext
    change 𝟙 _ ≫ 𝟙 _ ≫ U.output.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp)

local macro "grade_ext" : tactic =>
  `(tactic| (apply Pseudofunctor.StrongTrans.homCategory.ext; intro i; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply StructuredArrow.hom_ext))

def diagram (C : Type uC) [Category.{vC} C] : Pseudofunctor (Presentation.{vK,vL,vC,uK,uL,uC} C) (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) where
  obj A := output A.target
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
    grade_ext; change 𝟙 _ = 𝟙 _ ≫ V.output.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    rw [Functor.map_id]; simp
  map₂_left_unitor T := by
    grade_ext; change 𝟙 _ = 𝟙 _ ≫ T.output.map (𝟙 _) ≫ 𝟙 _
    simp
  map₂_right_unitor T := by
    grade_ext; change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp

end ContextualComposition.RelativeTensor.Presented.Output
