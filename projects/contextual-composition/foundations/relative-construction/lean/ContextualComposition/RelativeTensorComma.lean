module
public import ContextualComposition.RelativeTensorPresentedRecovery
public import ContextualComposition.RelativeTensorTargets

@[expose] public section
namespace ContextualComposition.RelativeTensor.Presented
open CategoryTheory Opposite Factorization
open scoped CategoryTheory.Bicategory
universe vK vL vC vD vE uK uL uC uD uE
variable {K : Type uK} {L : Type uL} {C : Type uC} {D : Type uD} {E : Type uE}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
variable (e : K ⥤ C) (d : L ⥤ C)
set_option backward.isDefEq.respectTransparency false

theorem write_read_native (S : Source.Cocone e d (D := D)) {s t : Object e d} (f : Source.ProductHom e d s t) :
    (write e d (read e d S)).map f = S.map f := by
  obtain ⟨i,p,q,x,y⟩ := s
  obtain ⟨j,p',q',x',y'⟩ := t
  obtain ⟨a,b,h,sq,tq⟩ := f
  change i = j at h
  subst j
  apply congrArg (fun k => S.map k)
  apply Source.ProductHom.ext <;> rfl

def writeReadIso (S : Source.Cocone e d (D := D)) : write e d (read e d S) ≅ S where
  hom := {
    app := fun _ => 𝟙 _
    native_naturality := fun f => (Category.comp_id _).trans ((write_read_native e d S f).trans (Category.id_comp _).symm)
    balance_naturality := fun x u y => (Category.comp_id _).trans (Category.id_comp _).symm }
  inv := {
    app := fun _ => 𝟙 _
    native_naturality := fun f => (Category.comp_id _).trans ((write_read_native e d S f).symm.trans (Category.id_comp _).symm)
    balance_naturality := fun x u y => (Category.comp_id _).trans (Category.id_comp _).symm }
  hom_inv_id := by apply Source.Transformation.ext; funext s; exact Category.id_comp _
  inv_hom_id := by apply Source.Transformation.ext; funext s; exact Category.id_comp _

def readWriteFiber (S : Cocone (input e) (output d) D) (i : C) : (read e d (write e d S)).fiber i ≅ S.fiber i :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y f
    change nativeMap e d S (Source.fibreProduct e d f) ≫ 𝟙 _ = 𝟙 _ ≫ _
    erw [native_fibre, Category.comp_id, Category.id_comp])

def readWriteIso (S : Cocone (input e) (output d) D) : read e d (write e d S) ≅ S where
  hom := ⟨fun i => (readWriteFiber e d S i).hom, fun u x y => (Category.comp_id _).trans (Category.id_comp _).symm⟩
  inv := ⟨fun i => (readWriteFiber e d S i).inv, fun u x y => (Category.comp_id _).trans (Category.id_comp _).symm⟩
  hom_inv_id := by apply Transformation.ext; funext i; exact (readWriteFiber e d S i).hom_inv_id
  inv_hom_id := by apply Transformation.ext; funext i; exact (readWriteFiber e d S i).inv_hom_id

def coconeEquivalence : Source.Cocone e d (D := D) ≌ Cocone (input e) (output d) D :=
  CategoryTheory.Equivalence.mk (readFunctor e d) (writeFunctor e d)
    (NatIso.ofComponents (fun S => (writeReadIso e d S).symm) (by
      intro S T f; apply Source.Transformation.ext; funext s
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (readWriteIso e d) (by
      intro S T f; apply Transformation.ext; funext i; apply NatTrans.ext; funext x
      exact (Category.comp_id _).trans (Category.id_comp _).symm))

noncomputable def commaPresentation (D : Type uD) [Category.{vD} D] :
    (Comma e d ⥤ D) ≌ Cocone (input e) (output d) D := (Endpoint.commaCoconeEquivalence e d D).trans (coconeEquivalence e d)

abbrev Carrier := Tensor (input e) (output d)

/-- Decode a tensor vertex by composing the two comma arrows; the underlying generic functor evaluates its product arrows and balance paths. -/
noncomputable def decode : Carrier e d ⥤ Comma e d := ((commaPresentation e d _).functor.obj (𝟭 _)).extend

theorem decode_object {i : C} (x : CostructuredArrow e i) (y : StructuredArrow i d) :
    (decode e d).obj ((insertion (input e) (output d) i).obj (x,y)) = Comma.mk x.left y.right (x.hom ≫ y.hom) := rfl

theorem decode_grades {i : C} {x x' : CostructuredArrow e i} {y y' : StructuredArrow i d} (α : x ⟶ x') (β : y ⟶ y') :
    ((decode e d).map ((insertion (input e) (output d) i).map (productMap α β))).left = α.left ∧
    ((decode e d).map ((insertion (input e) (output d) i).map (productMap α β))).right = β.right := by
  have h := ((commaPresentation e d _).functor.obj (𝟭 _)).extend_generator (Edge.native (F := input e) (G := output d) α β)
  exact ⟨congrArg CommaMorphism.left h, congrArg CommaMorphism.right h⟩

/-- The inverse representation is supplied by the actual comma presentation at the tensor target. -/
noncomputable def encode : Comma e d ⥤ Carrier e d := (commaPresentation e d _).inverse.obj (restrict (𝟭 _))

theorem read_target (S : Source.Cocone e d (D := D)) (H : D ⥤ E) :
    read e d (Source.postcompose e d S H) = RelativeTensor.postcompose (read e d S) H := rfl

noncomputable def commaTarget (F : Comma e d ⥤ D) (H : D ⥤ E) :
    RelativeTensor.postcompose ((commaPresentation e d D).functor.obj F) H ≅
      (commaPresentation e d E).functor.obj (F ⋙ H) :=
  (readFunctor e d).mapIso (Endpoint.commaCoconeTargetIso F H)

noncomputable def decodeEncode : decode e d ⋙ encode e d ≅ 𝟭 (Carrier e d) :=
  (universalProperty (F := input e) (G := output d) (D := Carrier e d)).fullyFaithfulFunctor.preimageIso
    (calc
      restrict (decode e d ⋙ encode e d) ≅ RelativeTensor.postcompose (restrict (decode e d)) (encode e d) := Iso.refl _
      _ ≅ RelativeTensor.postcompose ((commaPresentation e d _).functor.obj (𝟭 _)) (encode e d) :=
        (postFunctor (encode e d)).mapIso (coconeSection _)
      _ ≅ (commaPresentation e d _).functor.obj (𝟭 _ ⋙ encode e d) := commaTarget e d _ _
      _ ≅ (commaPresentation e d _).functor.obj (encode e d) := (commaPresentation e d _).functor.mapIso (Functor.leftUnitor _)
      _ ≅ restrict (𝟭 _) := (commaPresentation e d _).counitIso.app _)

noncomputable def encodeDecode : encode e d ⋙ decode e d ≅ 𝟭 (Comma e d) :=
  (commaPresentation e d _).fullyFaithfulFunctor.preimageIso
    (calc
      (commaPresentation e d _).functor.obj (encode e d ⋙ decode e d) ≅
        RelativeTensor.postcompose ((commaPresentation e d _).functor.obj (encode e d)) (decode e d) := (commaTarget e d _ _).symm
      _ ≅ RelativeTensor.postcompose (restrict (𝟭 (Carrier e d))) (decode e d) :=
        (postFunctor (decode e d)).mapIso ((commaPresentation e d _).counitIso.app _)
      _ ≅ restrict (decode e d) := (restrictFunctor (F := input e) (G := output d)).mapIso (Functor.leftUnitor (decode e d))
      _ ≅ (commaPresentation e d _).functor.obj (𝟭 _) := coconeSection _)

/-- The generic path-defined tensor of the two mixed comma factors is equivalent to the retained native comma category. -/
noncomputable def equivalence : Carrier e d ≌ Comma e d :=
  CategoryTheory.Equivalence.mk (decode e d) (encode e d) (decodeEncode e d).symm (encodeDecode e d)

end ContextualComposition.RelativeTensor.Presented
