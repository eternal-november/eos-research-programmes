module
public import ContextualComposition.EndpointTransport
@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor Source
universe vK vL vK' vL' vC vD vE vF uK uL uK' uL' uC uD uE uF
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'} {C : Type uC}
variable {D : Type uD} {E : Type uE} {F : Type uF}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L'] [Category.{vC} C]
variable [Category.{vD} D] [Category.{vE} E] [Category.{vF} F]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}

/-- Endpoint pullback preserves primitive inversion by the proved exact class criterion. -/
theorem precompose_inverts (T : Data e d e' d') (G : Object e' d' ⥤ D)
    (hG : (Primitive.generators e' d').IsInvertedBy G) :
    (Primitive.generators e d).IsInvertedBy (factorFunctor T ⋙ G) := by
  intro s t f hf
  apply (Primitive.inversion_iff e' d' G).mp hG ((factorFunctor T).map f)
  obtain ⟨hl,hr⟩ := Primitive.generators_le e d f hf
  let := hl
  let := hr
  exact ⟨T.input.map_isIso f.left, T.output.map_isIso f.right⟩

def invertingPullback (T : Data e d e' d') :
    (Primitive.generators e' d').FunctorsInverting D ⥤ (Primitive.generators e d).FunctorsInverting D where
  obj G := ⟨factorFunctor T ⋙ G.obj, precompose_inverts T G.obj G.property⟩
  map a := ⟨whiskerLeft (factorFunctor T) a.hom⟩
  map_id G := by apply InducedCategory.Hom.ext; rfl
  map_comp a b := by apply InducedCategory.Hom.ext; rfl

/-- Endpoint action on independent cocones, using the proved explicit extension. -/
noncomputable def pullback (T : Data e d e' d') (S : Cocone e' d' (D := D)) : Cocone e d (D := D) :=
  restrict e d (factorFunctor T ⋙ extensionFunctor e' d' S)
    (precompose_inverts T _ (extension_inverts e' d' S))

noncomputable def pullbackFunctor (T : Data e d e' d') :
    Cocone e' d' (D := D) ⥤ Cocone e d (D := D) :=
  extensionCategoryFunctor e' d' ⋙ invertingPullback T ⋙ restrictionFunctor e d

/-- No chosen preimage: the underlying functor is the actual endpoint composite. -/
noncomputable def extensionPullbackIso (T : Data e d e' d') (S : Cocone e' d' (D := D)) :
    extensionFunctor e d (pullback T S) ≅ factorFunctor T ⋙ extensionFunctor e' d' S :=
  extensionRestrictionIso e d _ (precompose_inverts T _ (extension_inverts e' d' S))

theorem pullback_obj (T : Data e d e' d') (S : Cocone e' d' (D := D)) (s : Object e d) :
    (pullback T S).obj s = S.obj ((factorFunctor T).obj s) := rfl

theorem pullback_product (T : Data e d e' d') (S : Cocone e' d' (D := D))
    {s t : Object e d} (f : ProductHom e d s t) :
    (pullback T S).map f = (extensionFunctor e' d' S).map ((factorFunctor T).map (productArrow e d f)) := rfl

theorem pullback_balance (T : Data e d e' d') (S : Cocone e' d' (D := D))
    (b : Primitive.Data e d) :
    ((pullback T S).bal b.x b.u b.y).hom =
      (extensionFunctor e' d' S).map ((factorFunctor T).map (Primitive.arrow e d b)) := rfl

/-- Actual interchange square: endpoint precomposition and target postcomposition. -/
noncomputable def pullbackPostcomposeIso (T : Data e d e' d') (S : Cocone e' d' (D := D)) (H : D ⥤ E) :
    postcompose e d (pullback T S) H ≅ pullback T (postcompose e' d' S H) := by
  let a := (Functor.associator (factorFunctor T) (extensionFunctor e' d' S) H) ≪≫
    isoWhiskerLeft (factorFunctor T) (extensionPostcomposeIso e' d' S H).symm
  exact (restrictionPostcomposeIso e d _ (precompose_inverts T _ (extension_inverts e' d' S)) H) ≪≫
    { hom := restrictTransformation e d _ _ _ _ a.hom
      inv := restrictTransformation e d _ _ _ _ a.inv
      hom_inv_id := by apply Transformation.ext; funext s; exact a.hom_inv_id_app s
      inv_hom_id := by apply Transformation.ext; funext s; exact a.inv_hom_id_app s }

/-- The square is natural in every independent cocone transformation. -/
noncomputable def pullbackTargetComparison (T : Data e d e' d') (H : D ⥤ E) :
    pullbackFunctor T ⋙ postcomposeFunctor e d H ≅
      postcomposeFunctor e' d' H ⋙ pullbackFunctor T :=
  NatIso.ofComponents (fun S => pullbackPostcomposeIso T S H) (by
    intro S R a
    apply Transformation.ext; funext s
    change H.map (a.app ((factorFunctor T).obj s)) ≫ (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) =
      (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫ H.map (a.app ((factorFunctor T).obj s))
    simp)

theorem pullback_target_naturality (T : Data e d e' d') (S : Cocone e' d' (D := D))
    {H J : D ⥤ E} (τ : H ⟶ J) :
    targetTransformation e d τ (pullback T S) ≫ (pullbackPostcomposeIso T S J).hom =
      (pullbackPostcomposeIso T S H).hom ≫
        (pullbackFunctor T).map (targetTransformation e' d' τ S) := by
  apply Transformation.ext; funext s
  change τ.app (S.obj ((factorFunctor T).obj s)) ≫ (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) =
    (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫ τ.app (S.obj ((factorFunctor T).obj s))
  simp

theorem pullback_target_identity (T : Data e d e' d') (S : Cocone e' d' (D := D)) :
    (pullbackPostcomposeIso T S (𝟭 D)).hom ≫ (pullbackFunctor T).map (postcomposeIdIso e' d' S).hom =
      (postcomposeIdIso e d (pullback T S)).hom := by
  apply Transformation.ext; funext s
  change (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫ 𝟙 _ = 𝟙 _
  simp

theorem pullback_target_composition (T : Data e d e' d') (S : Cocone e' d' (D := D))
    (H : D ⥤ E) (J : E ⥤ F) :
    (postcomposeCompIso e d (pullback T S) H J).hom ≫ (pullbackPostcomposeIso T S (H ⋙ J)).hom =
      postcomposeMap e d J (pullbackPostcomposeIso T S H).hom ≫
        (pullbackPostcomposeIso T (postcompose e' d' S H) J).hom ≫
        (pullbackFunctor T).map (postcomposeCompIso e' d' S H J).hom := by
  apply Transformation.ext; funext s
  change 𝟙 _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) = J.map (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫ (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫ 𝟙 _
  simp


/-- Restriction transports actual natural isomorphisms with their components unchanged. -/
def restrictIso {A B : Object e d ⥤ D}
    (hA : (Primitive.generators e d).IsInvertedBy A)
    (hB : (Primitive.generators e d).IsInvertedBy B) (a : A ≅ B) :
    restrict e d A hA ≅ restrict e d B hB where
  hom := restrictTransformation e d A B hA hB a.hom
  inv := restrictTransformation e d B A hB hA a.inv
  hom_inv_id := by apply Transformation.ext; funext s; exact a.hom_inv_id_app s
  inv_hom_id := by apply Transformation.ext; funext s; exact a.inv_hom_id_app s

noncomputable def pullbackRestrictionIso (T : Data e d e' d') (A : Object e' d' ⥤ D)
    (hA : (Primitive.generators e' d').IsInvertedBy A) :
    pullback T (restrict e' d' A hA) ≅ restrict e d (factorFunctor T ⋙ A) (precompose_inverts T A hA) :=
  restrictIso _ _ (isoWhiskerLeft (factorFunctor T) (extensionRestrictionIso e' d' A hA))

/-- Endpoint identity recovery is derived from the section of the presentation equivalence. -/
noncomputable def pullbackIdentityIso (S : Cocone e d (D := D)) :
    pullback (identityData e d) S ≅ S :=
  restrictIso _ _ (isoWhiskerRight factorIdentityIso (extensionFunctor e d S) ≪≫
    Functor.leftUnitor (extensionFunctor e d S)) ≪≫ restrictionExtensionIso e d S

universe vK'' vL'' uK'' uL''
variable {K'' : Type uK''} {L'' : Type uL''} [Category.{vK''} K''] [Category.{vL''} L'']
variable {e'' : K'' ⥤ C} {d'' : L'' ⥤ C}
/-- Composite endpoint pullback uses the proved extension recovery, not a functor-law assumption. -/
noncomputable def pullbackCompositionIso (T : Data e d e' d') (U : Data e' d' e'' d'')
    (S : Cocone e'' d'' (D := D)) :
    pullback T (pullback U S) ≅ pullback (composeData T U) S :=
  restrictIso _ _ (isoWhiskerLeft (factorFunctor T) (extensionPullbackIso U S) ≪≫
    (Functor.associator (factorFunctor T) (factorFunctor U) (extensionFunctor e'' d'' S)).symm ≪≫
    isoWhiskerRight (factorCompositionIso T U) (extensionFunctor e'' d'' S))

/-- The endpoint identity comparison commutes with changing target. -/
theorem pullback_identity_target (S : Cocone e d (D := D)) (H : D ⥤ E) :
    postcomposeMap e d H (pullbackIdentityIso S).hom =
      (pullbackPostcomposeIso (identityData e d) S H).hom ≫
        (pullbackIdentityIso (postcompose e d S H)).hom := by
  apply Transformation.ext; funext s
  change H.map (((extensionFunctor e d S).map (factorIdentityIso.hom.app s) ≫ 𝟙 _) ≫ 𝟙 _) =
    (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫ (((extensionFunctor e d (postcompose e d S H)).map (factorIdentityIso.hom.app s) ≫ 𝟙 _) ≫ 𝟙 _)
  simp only [Category.comp_id, Category.id_comp]
  have h := (extensionPostcomposeIso e d S H).hom.naturality (factorIdentityIso.hom.app s)
  change (extensionFunctor e d (postcompose e d S H)).map _ ≫ 𝟙 _ = 𝟙 _ ≫ H.map ((extensionFunctor e d S).map _) at h
  dsimp only [extensionFunctor, postcompose] at h ⊢
  simpa only [Category.comp_id, Category.id_comp] using h.symm

/-- Interchange respects endpoint composition, not only individual endpoint maps. -/
theorem pullback_composition_target (T : Data e d e' d') (U : Data e' d' e'' d'')
    (S : Cocone e'' d'' (D := D)) (H : D ⥤ E) :
    postcomposeMap e d H (pullbackCompositionIso T U S).hom ≫
      (pullbackPostcomposeIso (composeData T U) S H).hom =
    (pullbackPostcomposeIso T (pullback U S) H).hom ≫
      (pullbackFunctor T).map (pullbackPostcomposeIso U S H).hom ≫
      (pullbackCompositionIso T U (postcompose e'' d'' S H)).hom := by
  apply Transformation.ext; funext s
  change H.map (𝟙 _ ≫ 𝟙 _ ≫ (extensionFunctor e'' d'' S).map ((factorCompositionIso T U).hom.app s)) ≫
    (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) =
    (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫ (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫
      (𝟙 _ ≫ 𝟙 _ ≫ (extensionFunctor e'' d'' (postcompose e'' d'' S H)).map ((factorCompositionIso T U).hom.app s))
  simp only [Category.comp_id, Category.id_comp]
  have h := (extensionPostcomposeIso e'' d'' S H).hom.naturality ((factorCompositionIso T U).hom.app s)
  change (extensionFunctor e'' d'' (postcompose e'' d'' S H)).map _ ≫ 𝟙 _ = 𝟙 _ ≫ H.map ((extensionFunctor e'' d'' S).map _) at h
  dsimp only [extensionFunctor, postcompose] at h ⊢
  simpa only [Category.comp_id, Category.id_comp] using h.symm

/-- Weak endpoint-choice maps are retained through cocone extension. -/
noncomputable def pullbackChoiceIso {T U : Data e d e' d'} (a : ChoiceIso T U)
    (S : Cocone e' d' (D := D)) : pullback T S ≅ pullback U S :=
  restrictIso _ _ (isoWhiskerRight a.factorIso (extensionFunctor e' d' S))

theorem pullback_choice_target {T U : Data e d e' d'} (a : ChoiceIso T U)
    (S : Cocone e' d' (D := D)) (H : D ⥤ E) :
    postcomposeMap e d H (pullbackChoiceIso a S).hom ≫ (pullbackPostcomposeIso U S H).hom =
      (pullbackPostcomposeIso T S H).hom ≫ (pullbackChoiceIso a (postcompose e' d' S H)).hom := by
  apply Transformation.ext; funext s
  change H.map ((extensionFunctor e' d' S).map (a.factorIso.hom.app s)) ≫ (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) =
    (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫ (extensionFunctor e' d' (postcompose e' d' S H)).map (a.factorIso.hom.app s)
  simp only [Category.comp_id, Category.id_comp]
  have h := (extensionPostcomposeIso e' d' S H).hom.naturality (a.factorIso.hom.app s)
  change (extensionFunctor e' d' (postcompose e' d' S H)).map _ ≫ 𝟙 _ = 𝟙 _ ≫ H.map ((extensionFunctor e' d' S).map _) at h
  dsimp only [extensionFunctor, postcompose] at h ⊢
  simpa only [Category.comp_id, Category.id_comp] using h.symm



/-- Extension recovery and the interchange square form the same actual functor comparison. -/
theorem extension_pullback_target (T : Data e d e' d') (S : Cocone e' d' (D := D)) (H : D ⥤ E) :
    (extensionPostcomposeIso e d (pullback T S) H).hom ≫
      whiskerRight (extensionPullbackIso T S).hom H ≫
      (Functor.associator (factorFunctor T) (extensionFunctor e' d' S) H).hom =
    extensionTransformation e d (pullbackPostcomposeIso T S H).hom ≫
      (extensionPullbackIso T (postcompose e' d' S H)).hom ≫
      whiskerLeft (factorFunctor T) (extensionPostcomposeIso e' d' S H).hom := by
  apply NatTrans.ext; funext s
  change 𝟙 _ ≫ H.map (𝟙 _) ≫ 𝟙 _ = (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫ 𝟙 _ ≫ 𝟙 _
  simp

/-- Weak-choice composition is preserved, with the actual extension map of each choice. -/
theorem pullback_choice_composition {T U V : Data e d e' d'} (a : ChoiceIso T U)
    (b : ChoiceIso U V) (S : Cocone e' d' (D := D)) :
    (pullbackChoiceIso (a.trans b) S).hom = (pullbackChoiceIso a S).hom ≫ (pullbackChoiceIso b S).hom := by
  apply Transformation.ext; funext s
  change (extensionFunctor e' d' S).map ((a.trans b).factorIso.hom.app s) =
    (extensionFunctor e' d' S).map (a.factorIso.hom.app s) ≫ (extensionFunctor e' d' S).map (b.factorIso.hom.app s)
  rw [ChoiceIso.factor_trans]
  exact (extensionFunctor e' d' S).map_comp _ _

/-- Target interchange is natural on both variables simultaneously. -/
theorem pullback_interchange (T : Data e d e' d') {S R : Cocone e' d' (D := D)}
    (a : S ⟶ R) {H J : D ⥤ E} (τ : H ⟶ J) (s : Object e d) :
    H.map (a.app ((factorFunctor T).obj s)) ≫ τ.app (R.obj ((factorFunctor T).obj s)) =
      τ.app (S.obj ((factorFunctor T).obj s)) ≫ J.map (a.app ((factorFunctor T).obj s)) :=
  τ.naturality (a.app ((factorFunctor T).obj s))

end ContextualComposition.Factorization.Endpoint
