module
public import ContextualComposition.CoconeExtension
@[expose] public section
namespace ContextualComposition.Factorization.Source
open CategoryTheory CategoryTheory.Functor
universe vK vL vC vD vE vF uK uL uC uD uE uF
variable {K : Type uK} {L : Type uL} {C : Type uC}
variable {D : Type uD} {E : Type uE} {F : Type uF}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vC} C]
variable [Category.{vD} D] [Category.{vE} E] [Category.{vF} F]
variable (e : K ⥤ C) (d : L ⥤ C)

/-- Target change acts on independently specified cocone data. -/
def postcompose (S : Cocone e d (D := D)) (H : D ⥤ E) : Cocone e d (D := E) where
  obj s := H.obj (S.obj s)
  map f := H.map (S.map f)
  map_id s := by rw [S.map_id, H.map_id]
  map_comp f g := by rw [S.map_comp, H.map_comp]
  bal x u y := H.mapIso (S.bal x u y)
  bal_id x y := by change H.map (S.bal x (𝟙 _) y).hom = _; rw [S.bal_id]
  bal_comp x u v y := by
    change H.map (S.bal x (u ≫ v) y).hom = _
    rw [S.bal_comp, H.map_comp, H.map_comp, H.map_comp]
    rfl
  bal_natural x x' u y y' α β hx hy := by
    change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
    rw [← H.map_comp, ← H.map_comp, S.bal_natural]

def postcomposeMap (H : D ⥤ E) {S T : Cocone e d (D := D)} (a : S ⟶ T) :
    postcompose e d S H ⟶ postcompose e d T H where
  app s := H.map (a.app s)
  native_naturality f := by
    change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
    rw [← H.map_comp, ← H.map_comp, a.native_naturality]
  balance_naturality x u y := by
    change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
    rw [← H.map_comp, ← H.map_comp, a.balance_naturality]

def postcomposeFunctor (H : D ⥤ E) : Cocone e d (D := D) ⥤ Cocone e d (D := E) where
  obj S := postcompose e d S H
  map a := postcomposeMap e d H a
  map_id S := by apply Transformation.ext; funext s; exact H.map_id _
  map_comp a b := by apply Transformation.ext; funext s; exact H.map_comp _ _

/-- A natural transformation of target functors induces a cocone transformation. -/
def targetTransformation {H J : D ⥤ E} (τ : H ⟶ J) (S : Cocone e d (D := D)) :
    postcompose e d S H ⟶ postcompose e d S J where
  app s := τ.app (S.obj s)
  native_naturality f := τ.naturality (S.map f)
  balance_naturality x u y := τ.naturality (S.bal x u y).hom

/-- Naturality also holds in the independently specified cocone. -/
def targetNaturalTransformation {H J : D ⥤ E} (τ : H ⟶ J) :
    postcomposeFunctor e d H ⟶ postcomposeFunctor e d J where
  app S := targetTransformation e d τ S
  naturality S T a := by
    apply Transformation.ext; funext s
    exact τ.naturality (a.app s)

/-- Full functoriality on target functors and all their natural transformations. -/
def targetFunctor : (D ⥤ E) ⥤ (Cocone e d (D := D) ⥤ Cocone e d (D := E)) where
  obj H := postcomposeFunctor e d H
  map τ := targetNaturalTransformation e d τ
  map_id H := by apply NatTrans.ext; funext S; apply Transformation.ext; rfl
  map_comp τ σ := by apply NatTrans.ext; funext S; apply Transformation.ext; rfl

/-- Extension commutes with target change by actual functor equality. -/
theorem extension_postcompose (S : Cocone e d (D := D)) (H : D ⥤ E) :
    extensionFunctor e d (postcompose e d S H) = extensionFunctor e d S ⋙ H := by
  refine Functor.ext (F := extensionFunctor e d (postcompose e d S H)) (G := extensionFunctor e d S ⋙ H) (fun _ => rfl) ?_
  intro s t f
  change H.map (S.map (outputProduct e d f)) ≫ H.map (S.bal s.first f.middle t.second).hom ≫
      H.map (S.map (inputProduct e d f)) = 𝟙 _ ≫ H.map (extensionMap e d S f) ≫ 𝟙 _
  simp only [extensionMap, H.map_comp, Category.id_comp, Category.comp_id]
  exact congrArg (fun k => H.map (S.map (outputProduct e d f)) ≫ k) (H.map_comp (S.bal s.first f.middle t.second).hom (S.map (inputProduct e d f))).symm


/-- Target identity comparison on the independently specified cocone category. -/
def postcomposeIdIso (S : Cocone e d (D := D)) : postcompose e d S (𝟭 D) ≅ S where
  hom := ⟨fun _ => 𝟙 _, by intros; simp [postcompose], by intros; simp [postcompose]⟩
  inv := ⟨fun _ => 𝟙 _, by intros; simp [postcompose], by intros; simp [postcompose]⟩
  hom_inv_id := by apply Transformation.ext; funext s; exact Category.id_comp _
  inv_hom_id := by apply Transformation.ext; funext s; exact Category.id_comp _

/-- Target composition comparison, retaining actual transformation components. -/
def postcomposeCompIso (S : Cocone e d (D := D)) (H : D ⥤ E) (J : E ⥤ F) :
    postcompose e d (postcompose e d S H) J ≅ postcompose e d S (H ⋙ J) where
  hom := ⟨fun _ => 𝟙 _, by intros; simp [postcompose], by intros; simp [postcompose]⟩
  inv := ⟨fun _ => 𝟙 _, by intros; simp [postcompose], by intros; simp [postcompose]⟩
  hom_inv_id := by apply Transformation.ext; funext s; exact Category.id_comp _
  inv_hom_id := by apply Transformation.ext; funext s; exact Category.id_comp _

def postcomposeIdentity : postcomposeFunctor e d (𝟭 D) ≅ 𝟭 (Cocone e d (D := D)) :=
  NatIso.ofComponents (postcomposeIdIso e d) (by
    intro S T a
    apply Transformation.ext; funext s
    change a.app s ≫ 𝟙 _ = 𝟙 _ ≫ a.app s
    simp)

def postcomposeComposition (H : D ⥤ E) (J : E ⥤ F) :
    postcomposeFunctor e d H ⋙ postcomposeFunctor e d J ≅ postcomposeFunctor e d (H ⋙ J) :=
  NatIso.ofComponents (fun S => postcomposeCompIso e d S H J) (by
    intro S T a
    apply Transformation.ext; funext s
    change J.map (H.map (a.app s)) ≫ 𝟙 _ = 𝟙 _ ≫ J.map (H.map (a.app s))
    simp)

/-- Postcomposition of an inverting functor remains inverting. -/
theorem postcompose_inverts (G : Object e d ⥤ D)
    (hG : (Primitive.generators e d).IsInvertedBy G) (H : D ⥤ E) :
    (Primitive.generators e d).IsInvertedBy (G ⋙ H) :=
  MorphismProperty.IsInvertedBy.of_comp (Primitive.generators e d) G hG H

/-- The restriction comparison commutes with changing targets. -/
noncomputable def restrictionPostcomposeIso (G : Object e d ⥤ D)
    (hG : (Primitive.generators e d).IsInvertedBy G) (H : D ⥤ E) :
    postcompose e d (restrict e d G hG) H ≅
      restrict e d (G ⋙ H) (postcompose_inverts e d G hG H) where
  hom := ⟨fun _ => 𝟙 _, by intros; simp [postcompose, restrict], by intros; simp [postcompose, restrict, Primitive.arrow, asIso]⟩
  inv := ⟨fun _ => 𝟙 _, by intros; simp [postcompose, restrict], by intros; simp [postcompose, restrict, Primitive.arrow, asIso]⟩
  hom_inv_id := by apply Transformation.ext; funext s; exact Category.id_comp _
  inv_hom_id := by apply Transformation.ext; funext s; exact Category.id_comp _


/-- Left unit coherence includes the target functor's ordinary unitor. -/
theorem target_left_unit (S : Cocone e d (D := D)) (H : D ⥤ E) :
    postcomposeMap e d H (postcomposeIdIso e d S).hom =
      (postcomposeCompIso e d S (𝟭 D) H).hom ≫
      targetTransformation e d (Functor.leftUnitor H).hom S := by
  apply Transformation.ext; funext s
  change H.map (𝟙 _) = (𝟙 _) ≫ (𝟙 _)
  simp

theorem target_right_unit (S : Cocone e d (D := D)) (H : D ⥤ E) :
    (postcomposeIdIso e d (postcompose e d S H)).hom =
      (postcomposeCompIso e d S H (𝟭 E)).hom ≫
      targetTransformation e d (Functor.rightUnitor H).hom S := by
  apply Transformation.ext; funext s
  change (𝟙 _) = (𝟙 _) ≫ (𝟙 _)
  simp

universe vG uG
variable {G : Type uG} [Category.{vG} G]
/-- Associativity coherence, with all comparison routes and the target associator. -/
theorem target_associativity (S : Cocone e d (D := D))
    (H : D ⥤ E) (J : E ⥤ F) (N : F ⥤ G) :
    postcomposeMap e d N (postcomposeCompIso e d S H J).hom ≫
      (postcomposeCompIso e d S (H ⋙ J) N).hom ≫
      targetTransformation e d (Functor.associator H J N).hom S =
    (postcomposeCompIso e d (postcompose e d S H) J N).hom ≫
      (postcomposeCompIso e d S H (J ⋙ N)).hom := by
  apply Transformation.ext; funext s
  change N.map (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _) = (𝟙 _) ≫ (𝟙 _)
  simp

/-- Compatibility with right whiskering of a target natural transformation. -/
theorem target_whiskerRight {H H' : D ⥤ E} (τ : H ⟶ H') (J : E ⥤ F)
    (S : Cocone e d (D := D)) :
    targetTransformation e d (whiskerRight τ J) S =
      (postcomposeCompIso e d S H J).inv ≫
      postcomposeMap e d J (targetTransformation e d τ S) ≫
      (postcomposeCompIso e d S H' J).hom := by
  apply Transformation.ext; funext s
  change J.map (τ.app (S.obj s)) = (𝟙 _) ≫ J.map (τ.app (S.obj s)) ≫ (𝟙 _)
  simp

/-- Compatibility with left whiskering of a target natural transformation. -/
theorem target_whiskerLeft (H : D ⥤ E) {J J' : E ⥤ F} (τ : J ⟶ J')
    (S : Cocone e d (D := D)) :
    targetTransformation e d (whiskerLeft H τ) S =
      (postcomposeCompIso e d S H J).inv ≫
      targetTransformation e d τ (postcompose e d S H) ≫
      (postcomposeCompIso e d S H J').hom := by
  apply Transformation.ext; funext s
  change τ.app (H.obj (S.obj s)) = (𝟙 _) ≫ τ.app (H.obj (S.obj s)) ≫ (𝟙 _)
  simp

/-- Target change on the category of primitive-inverting functors. -/
def invertingPostcomposeFunctor (H : D ⥤ E) :
    (Primitive.generators e d).FunctorsInverting D ⥤
      (Primitive.generators e d).FunctorsInverting E where
  obj A := ⟨A.obj ⋙ H, postcompose_inverts e d A.obj A.property H⟩
  map a := ⟨whiskerRight a.hom H⟩
  map_id A := by apply InducedCategory.Hom.ext; apply NatTrans.ext; funext s; exact H.map_id _
  map_comp a b := by apply InducedCategory.Hom.ext; apply NatTrans.ext; funext s; exact H.map_comp _ _

/-- Actual natural comparison square for the equivalence's restriction functor. -/
noncomputable def restrictionTargetComparison (H : D ⥤ E) :
    restrictionFunctor e d ⋙ postcomposeFunctor e d H ≅
      invertingPostcomposeFunctor e d H ⋙ restrictionFunctor e d :=
  NatIso.ofComponents (fun A => restrictionPostcomposeIso e d A.obj A.property H) (by
    intro A B a
    apply Transformation.ext; funext s
    change H.map (a.hom.app s) ≫ (𝟙 _) = (𝟙 _) ≫ H.map (a.hom.app s)
    simp)

/-- The restriction comparison square is natural in target transformations too. -/
theorem restriction_target_naturality (A : Object e d ⥤ D)
    (hA : (Primitive.generators e d).IsInvertedBy A) {H J : D ⥤ E} (τ : H ⟶ J) :
    targetTransformation e d τ (restrict e d A hA) ≫
      (restrictionPostcomposeIso e d A hA J).hom =
    (restrictionPostcomposeIso e d A hA H).hom ≫
      restrictTransformation e d (A ⋙ H) (A ⋙ J)
        (postcompose_inverts e d A hA H) (postcompose_inverts e d A hA J)
        (whiskerLeft A τ) := by
  apply Transformation.ext; funext s
  change τ.app (A.obj s) ≫ (𝟙 _) = (𝟙 _) ≫ τ.app (A.obj s)
  simp


/-- Identity coherence of the restriction square, including the functor unitor. -/
theorem restriction_target_identity (A : Object e d ⥤ D)
    (hA : (Primitive.generators e d).IsInvertedBy A) :
    (postcomposeIdIso e d (restrict e d A hA)).hom =
      (restrictionPostcomposeIso e d A hA (𝟭 D)).hom ≫
      restrictTransformation e d (A ⋙ 𝟭 D) A
        (postcompose_inverts e d A hA (𝟭 D)) hA (Functor.rightUnitor A).hom := by
  apply Transformation.ext; funext s
  change (𝟙 _) = (𝟙 _) ≫ (𝟙 _)
  simp

/-- Composition coherence of the restriction square, with the ordinary associator. -/
theorem restriction_target_composition (A : Object e d ⥤ D)
    (hA : (Primitive.generators e d).IsInvertedBy A) (H : D ⥤ E) (J : E ⥤ F) :
    (postcomposeCompIso e d (restrict e d A hA) H J).hom ≫
      (restrictionPostcomposeIso e d A hA (H ⋙ J)).hom =
    postcomposeMap e d J (restrictionPostcomposeIso e d A hA H).hom ≫
      (restrictionPostcomposeIso e d (A ⋙ H) (postcompose_inverts e d A hA H) J).hom ≫
      restrictTransformation e d ((A ⋙ H) ⋙ J) (A ⋙ (H ⋙ J))
        (postcompose_inverts e d (A ⋙ H) (postcompose_inverts e d A hA H) J)
        (postcompose_inverts e d A hA (H ⋙ J)) (Functor.associator A H J).hom := by
  apply Transformation.ext; funext s
  change (𝟙 _) ≫ (𝟙 _) = J.map (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _)
  simp

/-- Extension on arbitrary cocone transformations, rather than only restricted ones. -/
def extensionTransformation {S T : Cocone e d (D := D)} (a : S ⟶ T) :
    extensionFunctor e d S ⟶ extensionFunctor e d T :=
  Primitive.transformationOfGenerators e d (extensionFunctor e d S) (extensionFunctor e d T) a.app
    (fun f => by
      change extensionMap e d S (productArrow e d (outputProduct e d f)) ≫ a.app _ =
        a.app _ ≫ extensionMap e d T (productArrow e d (outputProduct e d f))
      rw [extensionMap_product, extensionMap_product]
      exact a.native_naturality _)
    (fun f => by
      change extensionMap e d S (productArrow e d (inputProduct e d f)) ≫ a.app _ =
        a.app _ ≫ extensionMap e d T (productArrow e d (inputProduct e d f))
      rw [extensionMap_product, extensionMap_product]
      exact a.native_naturality _)
    (fun b => by
      change extensionMap e d S (balance e d b.P b.Q b.x b.u b.y) ≫ a.app _ =
        a.app _ ≫ extensionMap e d T (balance e d b.P b.Q b.x b.u b.y)
      rw [extensionMap_balance, extensionMap_balance]
      exact a.balance_naturality _ _ _)

/-- The explicit extension is a functor between the two presentation categories. -/
def extensionCategoryFunctor : Cocone e d (D := D) ⥤ (Primitive.generators e d).FunctorsInverting D where
  obj S := ⟨extensionFunctor e d S, extension_inverts e d S⟩
  map a := ⟨extensionTransformation e d a⟩
  map_id S := by apply InducedCategory.Hom.ext; apply NatTrans.ext; rfl
  map_comp a b := by apply InducedCategory.Hom.ext; apply NatTrans.ext; rfl

/-- Target change commutes with the explicit extension on all components. -/
theorem extension_transformation_postcompose {S T : Cocone e d (D := D)} (a : S ⟶ T)
    (H : D ⥤ E) (s : Object e d) :
    (extensionTransformation e d (postcomposeMap e d H a)).app s =
      H.map ((extensionTransformation e d a).app s) := rfl


/-- The explicit inverse comparison is natural in all inverting functors. -/
noncomputable def explicitUnitIso :
    𝟭 ((Primitive.generators e d).FunctorsInverting D) ≅
      restrictionFunctor e d ⋙ extensionCategoryFunctor e d :=
  NatIso.ofComponents (fun A => InducedCategory.isoMk (extensionRestrictionIso e d A.obj A.property).symm) (by
    intro A B a
    apply InducedCategory.Hom.ext; apply NatTrans.ext; funext s
    change a.hom.app s ≫ (𝟙 _) = (𝟙 _) ≫ a.hom.app s
    simp)

/-- The independent-cocone comparison is natural in all cocone transformations. -/
noncomputable def explicitCounitIso :
    extensionCategoryFunctor e d ⋙ restrictionFunctor e d ≅ 𝟭 (Cocone e d (D := D)) :=
  NatIso.ofComponents (restrictionExtensionIso e d) (by
    intro S T a
    apply Transformation.ext; funext s
    change a.app s ≫ (𝟙 _) = (𝟙 _) ≫ a.app s
    simp)

/-- A presentation equivalence whose inverse is the explicit extension functor. -/
noncomputable def explicitPresentationEquivalence :
    (Primitive.generators e d).FunctorsInverting D ≌ Cocone e d (D := D) where
  functor := restrictionFunctor e d
  inverse := extensionCategoryFunctor e d
  unitIso := explicitUnitIso e d
  counitIso := explicitCounitIso e d
  functor_unitIso_comp A := by
    apply Transformation.ext; funext s
    change (𝟙 _) ≫ (𝟙 _) = (𝟙 _)
    simp

/-- Identity-component comparison for explicit extension under target change. -/
def extensionPostcomposeIso (S : Cocone e d (D := D)) (H : D ⥤ E) :
    extensionFunctor e d (postcompose e d S H) ≅ extensionFunctor e d S ⋙ H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro s t f
    change extensionMap e d (postcompose e d S H) f ≫ 𝟙 _ = 𝟙 _ ≫ H.map (extensionMap e d S f)
    rw [Category.comp_id, Category.id_comp]
    change H.map (S.map (outputProduct e d f)) ≫ H.map (S.bal s.first f.middle t.second).hom ≫
      H.map (S.map (inputProduct e d f)) = H.map (extensionMap e d S f)
    exact ((H.map_comp (S.map (outputProduct e d f))
      ((S.bal s.first f.middle t.second).hom ≫ S.map (inputProduct e d f))).trans
      (congrArg (fun k => H.map (S.map (outputProduct e d f)) ≫ k)
        (H.map_comp (S.bal s.first f.middle t.second).hom (S.map (inputProduct e d f))))).symm)

/-- Natural target-change square for the explicit inverse, not a chosen preimage. -/
def extensionTargetComparison (H : D ⥤ E) :
    postcomposeFunctor e d H ⋙ extensionCategoryFunctor e d ≅
      extensionCategoryFunctor e d ⋙ invertingPostcomposeFunctor e d H :=
  NatIso.ofComponents (fun S => InducedCategory.isoMk (extensionPostcomposeIso e d S H)) (by
    intro S T a
    apply InducedCategory.Hom.ext; apply NatTrans.ext; funext s
    change H.map (a.app s) ≫ (𝟙 _) = (𝟙 _) ≫ H.map (a.app s)
    simp)


/-- Target-change compatibility of the explicit cocone comparison (counit). -/
theorem target_counit_compatibility (S : Cocone e d (D := D)) (H : D ⥤ E) :
    postcomposeMap e d H (restrictionExtensionIso e d S).hom =
    (restrictionPostcomposeIso e d (extensionFunctor e d S) (extension_inverts e d S) H).hom ≫
      restrictTransformation e d (extensionFunctor e d S ⋙ H)
        (extensionFunctor e d (postcompose e d S H))
        (postcompose_inverts e d (extensionFunctor e d S) (extension_inverts e d S) H)
        (extension_inverts e d (postcompose e d S H)) (extensionPostcomposeIso e d S H).inv ≫
      (restrictionExtensionIso e d (postcompose e d S H)).hom := by
  apply Transformation.ext; funext s
  change H.map (𝟙 _) = (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _)
  simp

/-- Target-change compatibility of the original-functor recovery (inverse unit). -/
theorem target_unit_compatibility (A : Object e d ⥤ D)
    (hA : (Primitive.generators e d).IsInvertedBy A) (H : D ⥤ E) :
    whiskerRight (extensionRestrictionIso e d A hA).hom H =
      (extensionPostcomposeIso e d (restrict e d A hA) H).inv ≫
      extensionTransformation e d (restrictionPostcomposeIso e d A hA H).hom ≫
      (extensionRestrictionIso e d (A ⋙ H) (postcompose_inverts e d A hA H)).hom := by
  apply NatTrans.ext; funext s
  change H.map (𝟙 _) = (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _)
  simp


/-- Identity coherence for the explicit extension target square. -/
theorem extension_target_identity (S : Cocone e d (D := D)) :
    (extensionPostcomposeIso e d S (𝟭 D)).hom ≫
      (Functor.rightUnitor (extensionFunctor e d S)).hom =
    extensionTransformation e d (postcomposeIdIso e d S).hom := by
  apply NatTrans.ext; funext s
  change (𝟙 _) ≫ (𝟙 _) = (𝟙 _)
  simp

/-- Composition coherence for the explicit extension target square. -/
theorem extension_target_composition (S : Cocone e d (D := D)) (H : D ⥤ E) (J : E ⥤ F) :
    extensionTransformation e d (postcomposeCompIso e d S H J).hom ≫
      (extensionPostcomposeIso e d S (H ⋙ J)).hom =
    (extensionPostcomposeIso e d (postcompose e d S H) J).hom ≫
      whiskerRight (extensionPostcomposeIso e d S H).hom J ≫
      (Functor.associator (extensionFunctor e d S) H J).hom := by
  apply NatTrans.ext; funext s
  change (𝟙 _) ≫ (𝟙 _) = (𝟙 _) ≫ J.map (𝟙 _) ≫ (𝟙 _)
  simp

/-- Naturality of the extension target square in every target transformation. -/
theorem extension_target_naturality (S : Cocone e d (D := D)) {H J : D ⥤ E} (τ : H ⟶ J) :
    extensionTransformation e d (targetTransformation e d τ S) ≫
      (extensionPostcomposeIso e d S J).hom =
    (extensionPostcomposeIso e d S H).hom ≫ whiskerLeft (extensionFunctor e d S) τ := by
  apply NatTrans.ext; funext s
  change τ.app (S.obj s) ≫ (𝟙 _) = (𝟙 _) ≫ τ.app (S.obj s)
  simp

end ContextualComposition.Factorization.Source
