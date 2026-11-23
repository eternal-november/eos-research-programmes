module
public import ContextualComposition.RelativeTensorPresentedDiagram
public import ContextualComposition.IndexedNormalization

@[expose] public section
namespace ContextualComposition.RelativeTensor.Presented
open CategoryTheory Opposite Factorization
open scoped CategoryTheory.Bicategory
universe vK vL vC uK uL uC
variable {C : Type uC} [Category.{vC} C]
variable {A B D : Endpoint.Presentation.{vK,vL,vC,uK,uL,uC} C}
set_option backward.isDefEq.respectTransparency false

private theorem identitySquare (A : Endpoint.Presentation.{vK,vL,vC,uK,uL,uC} C) (s : Carrier A.source A.target) :
    (normalizationComponent (𝟙 A) s).hom ≫ Endpoint.commaIdentityIso.hom.app ((decode A.source A.target).obj s) =
      (decode A.source A.target).map (((tensorDiagram C).mapId A).hom.toNatTrans.app s) := by
  have h := decodedUnit A s
  apply Comma.hom_ext
  · change 𝟙 _ ≫ 𝟙 _ = _
    exact (Category.id_comp _).trans h.1.symm
  · change 𝟙 _ ≫ 𝟙 _ = _
    exact (Category.id_comp _).trans h.2.symm

private theorem compositeSquare (T : A ⟶ B) (U : B ⟶ D) (s : Carrier A.source A.target) :
    (normalizationComponent (T ≫ U) s).hom ≫ (Endpoint.commaCompositionIso T U).inv.app ((decode A.source A.target).obj s) =
      (decode D.source D.target).map (((tensorDiagram C).mapComp T U).hom.toNatTrans.app s) ≫
      (normalizationComponent U ((tensorTransport T).obj s)).hom ≫
      (Endpoint.commaFunctor U).map (normalizationComponent T s).hom := by
  have h := decodedComposite T U s
  apply Comma.hom_ext
  · change 𝟙 _ ≫ 𝟙 _ = _ ≫ 𝟙 _ ≫ U.input.map (𝟙 _)
    erw [h.1,Functor.map_id,Category.id_comp,Category.id_comp]
  · change 𝟙 _ ≫ 𝟙 _ = _ ≫ 𝟙 _ ≫ U.output.map (𝟙 _)
    erw [h.2,Functor.map_id,Category.id_comp,Category.id_comp]

private theorem padUnit {X Y : Type*} [Category* X] [Category* Y] (F : X ⥤ Y) {a b : X} {p : Y}
    (f : F.obj a ⟶ p) (g : p ⟶ F.obj b) (k : a ⟶ b) (h : f ≫ g = F.map k) :
    f ≫ (g ≫ 𝟙 _) = F.map (k ≫ 𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ := by simpa using h

private theorem padComp {X Y : Type*} [Category* X] [Category* Y] (F : X ⥤ Y) {a b : X} {p q r : Y}
    (f : F.obj a ⟶ p) (g : p ⟶ r) (k : a ⟶ b) (l : F.obj b ⟶ q) (m : q ⟶ r)
    (h : f ≫ g = F.map k ≫ l ≫ m) :
    f ≫ (g ≫ 𝟙 _) = F.map (k ≫ 𝟙 _) ≫ 𝟙 _ ≫ l ≫ 𝟙 _ ≫ m ≫ 𝟙 _ := by simpa using h

/-- Global comma normalization for the independently defined relative tensor of the two represented factors. -/
noncomputable def normalization (C : Type uC) [Category.{vC} C] :
    Pseudofunctor.StrongTrans (largeTensor.{vK,vL,vC,uK,uL,uC} C) (Endpoint.Presentation.largeComma C) where
  app A := (Endpoint.UniverseLift.map (decode A.source A.target)).toCatHom
  naturality T := Cat.Hom.isoMk (Endpoint.UniverseLift.iso (normalizationSquare T))
  naturality_naturality m := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext
    have h := decodedChoice m (ULift.down x)
    apply Comma.hom_ext
    · change _ ≫ 𝟙 _ = 𝟙 _ ≫ m.input.hom.app _
      erw [Category.comp_id,Category.id_comp,h.1]
      rfl
    · change _ ≫ 𝟙 _ = 𝟙 _ ≫ m.output.hom.app _
      erw [Category.comp_id,Category.id_comp,h.2]
      rfl
  naturality_id A := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext
    exact padUnit (decode A.source A.target) _ _ _ (identitySquare A (ULift.down x))
  naturality_comp T U := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext
    exact padComp (decode _ _) _ _ _ _ _ (compositeSquare T U (ULift.down x))

/-- Specialization to the source's independent context and content extension functors on their Grothendieck total categories. -/
noncomputable def indexedNormalization
    (K : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vK,uK}) (L : LocallyDiscrete C ⥤ᵖ Cat.{vL,uL})
    (e : Pseudofunctor.CoGrothendieck K ⥤ C) (d : Pseudofunctor.Grothendieck L ⥤ C) :=
  Endpoint.Indexed.reindex (Endpoint.Indexed.action K L e d) (normalization C)

end ContextualComposition.RelativeTensor.Presented
