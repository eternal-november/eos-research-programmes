module
public import ContextualComposition.EndpointTarget
@[expose] public section
namespace ContextualComposition.Factorization.Descent
open CategoryTheory CategoryTheory.Functor
universe vA vB vE uA uB uE
variable {A : Type uA} {B : Type uB} {E : Type uE}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vE} E]
variable (Q : A ⥤ B) (W : MorphismProperty A) [Q.IsLocalization W]
/-- A chosen lift with its actual comparison, not equality of composite functors. -/
structure Lift where
  source : A ⥤ E
  target : B ⥤ E
  comparison : Q ⋙ target ≅ source
variable {Q W}
noncomputable def map (X Y : Lift Q (E := E)) (a : X.source ⟶ Y.source) : X.target ⟶ Y.target := by
  letI : Localization.Lifting Q W X.source X.target := ⟨X.comparison⟩
  letI : Localization.Lifting Q W Y.source Y.target := ⟨Y.comparison⟩
  exact Localization.liftNatTrans Q W X.source Y.source X.target Y.target a
@[simp] theorem map_app (X Y : Lift Q (E := E)) (a : X.source ⟶ Y.source) (s : A) :
    (map (W := W) X Y a).app (Q.obj s) =
      X.comparison.hom.app s ≫ a.app s ≫ Y.comparison.inv.app s := by
  let : Localization.Lifting Q W X.source X.target := ⟨X.comparison⟩
  let : Localization.Lifting Q W Y.source Y.target := ⟨Y.comparison⟩
  exact Localization.liftNatTrans_app Q W X.source Y.source X.target Y.target a s
/- Faithfulness checks diagrams on original objects with comparison conjugations retained. -/
include W in
theorem ext {X Y : B ⥤ E} {a b : X ⟶ Y}
    (h : ∀ s, a.app (Q.obj s) = b.app (Q.obj s)) : a = b :=
  Localization.natTrans_ext Q W h
@[simp] theorem map_id (X : Lift Q (E := E)) : map (W := W) X X (𝟙 X.source) = 𝟙 X.target := by
  apply ext (Q := Q) (W := W); intro s
  simp
@[simp] theorem map_comp (X Y Z : Lift Q (E := E)) (a : X.source ⟶ Y.source) (b : Y.source ⟶ Z.source) :
    map (W := W) X Z (a ≫ b) = map (W := W) X Y a ≫ map (W := W) Y Z b := by
  apply ext (Q := Q) (W := W); intro s
  simp [Category.assoc]
noncomputable def iso (X Y : Lift Q (E := E)) (a : X.source ≅ Y.source) : X.target ≅ Y.target where
  hom := map (W := W) X Y a.hom
  inv := map (W := W) Y X a.inv
  hom_inv_id := by rw [← map_comp, a.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, a.inv_hom_id, map_id]
/-- Equality of actual source composites descends. -/
theorem square (X Y Z R : Lift Q (E := E)) (a : X.source ⟶ Y.source) (b : Y.source ⟶ R.source)
    (c : X.source ⟶ Z.source) (d : Z.source ⟶ R.source) (h : a ≫ b = c ≫ d) :
    map (W := W) X Y a ≫ map (W := W) Y R b = map (W := W) X Z c ≫ map (W := W) Z R d := by
  rw [← map_comp, ← map_comp, h]
end ContextualComposition.Factorization.Descent
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor
universe vK vL vK' vL' vC uK uL uK' uL' uC
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'} {C : Type uC}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L'] [Category.{vC} C]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}
noncomputable def chosenLift (T : Data e d e' d') :
    Descent.Lift (Primitive.generators e d).Q (E := (Primitive.generators e' d').Localization) where
  source := factorFunctor T ⋙ (Primitive.generators e' d').Q
  target := localizedFactorFunctor T
  comparison := Localization.fac _ (factor_inverts T) (Primitive.generators e d).Q
noncomputable def identityLift (e : K ⥤ C) (d : L ⥤ C) :
    Descent.Lift (Primitive.generators e d).Q (E := (Primitive.generators e d).Localization) where
  source := (Primitive.generators e d).Q
  target := 𝟭 _
  comparison := Functor.rightUnitor _
noncomputable def localizedIdentityIso : localizedFactorFunctor (identityData e d) ≅ 𝟭 _ :=
  Descent.iso (W := Primitive.generators e d) (chosenLift _) (identityLift e d)
    (isoWhiskerRight factorIdentityIso (Primitive.generators e d).Q ≪≫ Functor.leftUnitor _)
universe vK'' vL'' uK'' uL''
variable {K'' : Type uK''} {L'' : Type uL''} [Category.{vK''} K''] [Category.{vL''} L'']
variable {e'' : K'' ⥤ C} {d'' : L'' ⥤ C}
/-- Composite lift comparison retains both factorization isomorphisms and all associators. -/
noncomputable def compositeLift (T : Data e d e' d') (U : Data e' d' e'' d'') :
    Descent.Lift (Primitive.generators e d).Q (E := (Primitive.generators e'' d'').Localization) where
  source := (factorFunctor T ⋙ factorFunctor U) ⋙ (Primitive.generators e'' d'').Q
  target := localizedFactorFunctor T ⋙ localizedFactorFunctor U
  comparison := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (chosenLift T).comparison (localizedFactorFunctor U) ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft (factorFunctor T) (chosenLift U).comparison ≪≫
    (Functor.associator _ _ _).symm
noncomputable def localizedCompositionIso (T : Data e d e' d') (U : Data e' d' e'' d'') :
    localizedFactorFunctor T ⋙ localizedFactorFunctor U ≅ localizedFactorFunctor (composeData T U) :=
  Descent.iso (W := Primitive.generators e d) (compositeLift T U) (chosenLift (composeData T U))
    (isoWhiskerRight (factorCompositionIso T U) (Primitive.generators e'' d'').Q)
noncomputable def localizedChoiceIso {T U : Data e d e' d'} (a : ChoiceIso T U) :
    localizedFactorFunctor T ≅ localizedFactorFunctor U :=
  Descent.iso (W := Primitive.generators e d) (chosenLift T) (chosenLift U)
    (isoWhiskerRight a.factorIso (Primitive.generators e' d').Q)
@[simp] theorem localizedChoice_app {T U : Data e d e' d'} (a : ChoiceIso T U) (s : Object e d) :
    (localizedChoiceIso a).hom.app ((Primitive.generators e d).Q.obj s) =
      (chosenLift T).comparison.hom.app s ≫ (Primitive.generators e' d').Q.map (a.factorIso.hom.app s) ≫
        (chosenLift U).comparison.inv.app s := Descent.map_app _ _ _ _
theorem localized_choice_composition {T U V : Data e d e' d'} (a : ChoiceIso T U) (b : ChoiceIso U V) :
    (localizedChoiceIso (a.trans b)).hom = (localizedChoiceIso a).hom ≫ (localizedChoiceIso b).hom := by
  apply Descent.ext (Q := (Primitive.generators e d).Q) (W := Primitive.generators e d); intro s
  simp only [localizedChoice_app, NatTrans.comp_app, ChoiceIso.factor_trans,
    (Primitive.generators e' d').Q.map_comp]
  dsimp only [chosenLift, localizedFactorFunctor]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]


@[simp] theorem localizedComposition_app (T : Data e d e' d') (U : Data e' d' e'' d'') (s : Object e d) :
    (localizedCompositionIso T U).hom.app ((Primitive.generators e d).Q.obj s) =
      (localizedFactorFunctor U).map ((chosenLift T).comparison.hom.app s) ≫
      (chosenLift U).comparison.hom.app ((factorFunctor T).obj s) ≫
      (Primitive.generators e'' d'').Q.map ((factorCompositionIso T U).hom.app s) ≫
      (chosenLift (composeData T U)).comparison.inv.app s := by
  change (Descent.map (W := Primitive.generators e d) _ _ _).app _ = _
  rw [Descent.map_app]
  dsimp only [compositeLift, chosenLift, localizedFactorFunctor]
  simp

@[simp] theorem localizedIdentity_app (s : Object e d) :
    localizedIdentityIso.hom.app ((Primitive.generators e d).Q.obj s) =
      (chosenLift (identityData e d)).comparison.hom.app s ≫
      (Primitive.generators e d).Q.map (factorIdentityIso.hom.app s) := by
  change (Descent.map (W := Primitive.generators e d) _ _ _).app _ = _
  rw [Descent.map_app]
  dsimp only [chosenLift, identityLift, localizedFactorFunctor]
  simp

universe vK''' vL''' uK''' uL'''
variable {K''' : Type uK'''} {L''' : Type uL'''} [Category.{vK'''} K'''] [Category.{vL'''} L''']
variable {e''' : K''' ⥤ C} {d''' : L''' ⥤ C}

/- Associativity compares actual chosen localized routes, including the weak-choice associator. -/
set_option backward.isDefEq.respectTransparency false in
theorem localized_associativity (T : Data e d e' d') (U : Data e' d' e'' d'')
    (V : Data e'' d'' e''' d''') :
    whiskerRight (localizedCompositionIso T U).hom (localizedFactorFunctor V) ≫
      (localizedCompositionIso (composeData T U) V).hom ≫
      (localizedChoiceIso (associatorChoice T U V)).hom =
    (Functor.associator (localizedFactorFunctor T) (localizedFactorFunctor U) (localizedFactorFunctor V)).hom ≫
      whiskerLeft (localizedFactorFunctor T) (localizedCompositionIso U V).hom ≫
      (localizedCompositionIso T (composeData U V)).hom := by
  apply Descent.ext (Q := (Primitive.generators e d).Q) (W := Primitive.generators e d)
  intro s
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, localizedComposition_app, localizedChoice_app]
  dsimp only [chosenLift, localizedFactorFunctor]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [← (localizedCompositionIso U V).hom.naturality_assoc ((chosenLift T).comparison.hom.app s)]
  erw [localizedComposition_app]
  dsimp only [chosenLift, localizedFactorFunctor, Functor.comp_map]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [((localizedFactorFunctor V).mapIso ((chosenLift (composeData T U)).comparison.app s)).inv_hom_id_assoc]
  erw [(chosenLift V).comparison.hom.naturality_assoc ((factorCompositionIso T U).hom.app s)]
  dsimp only [chosenLift, localizedFactorFunctor, Functor.comp_map]
  have h := congrArg ((Primitive.generators e''' d''').Q.map) (factor_associativity T U V s)
  simp only [Functor.map_comp] at h
  congr 1
  congr 1
  congr 1
  have h' := congrArg (fun f => f ≫ (chosenLift (composeData T (composeData U V))).comparison.inv.app s) h
  dsimp only [chosenLift, localizedFactorFunctor, Functor.comp_obj] at h' ⊢
  simpa only [Category.assoc] using h'

set_option backward.isDefEq.respectTransparency false in
theorem localized_left_unit (T : Data e d e' d') :
    whiskerRight localizedIdentityIso.hom (localizedFactorFunctor T) ≫
      (Functor.leftUnitor (localizedFactorFunctor T)).hom =
    (localizedCompositionIso (identityData e d) T).hom ≫
      (localizedChoiceIso (leftUnitChoice T)).hom := by
  apply Descent.ext (Q := (Primitive.generators e d).Q) (W := Primitive.generators e d)
  intro s
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.leftUnitor_hom_app,
    localizedIdentity_app, localizedComposition_app, localizedChoice_app]
  dsimp only [chosenLift, localizedFactorFunctor]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  have h := congrArg ((Primitive.generators e' d').Q.map) (factor_left_unit T s)
  simp only [Functor.map_comp] at h
  erw [← Category.assoc ((Primitive.generators e' d').Q.map ((factorCompositionIso (identityData e d) T).hom.app s)), ← h]
  erw [← (chosenLift T).comparison.hom.naturality_assoc (factorIdentityIso.hom.app s)]
  dsimp only [chosenLift, localizedFactorFunctor, Functor.comp_obj, Functor.comp_map]
  dsimp only [Functor.id_obj]
  simp only [Iso.hom_inv_id_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem localized_right_unit (T : Data e d e' d') :
    whiskerLeft (localizedFactorFunctor T) localizedIdentityIso.hom ≫
      (Functor.rightUnitor (localizedFactorFunctor T)).hom =
    (localizedCompositionIso T (identityData e' d')).hom ≫
      (localizedChoiceIso (rightUnitChoice T)).hom := by
  apply Descent.ext (Q := (Primitive.generators e d).Q) (W := Primitive.generators e d)
  intro s
  simp only [NatTrans.comp_app, whiskerLeft_app, Functor.rightUnitor_hom_app,
    localizedComposition_app, localizedChoice_app]
  dsimp only [chosenLift, localizedFactorFunctor]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have h := congrArg ((Primitive.generators e' d').Q.map) (factor_right_unit T s)
  simp only [Functor.map_comp] at h
  erw [← Category.assoc ((Primitive.generators e' d').Q.map ((factorCompositionIso T (identityData e' d')).hom.app s)), ← h]
  erw [← Category.assoc ((chosenLift (identityData e' d')).comparison.hom.app ((factorFunctor T).obj s)), ← localizedIdentity_app]
  erw [localizedIdentityIso.hom.naturality_assoc ((chosenLift T).comparison.hom.app s)]
  dsimp only [chosenLift, localizedFactorFunctor, Functor.id_map]
  simp only [Iso.hom_inv_id_app]
  rfl

theorem localized_choice_identity (T : Data e d e' d') :
    (localizedChoiceIso (ChoiceIso.refl T)).hom = 𝟙 (localizedFactorFunctor T) := by
  apply Descent.ext (Q := (Primitive.generators e d).Q) (W := Primitive.generators e d)
  intro s
  rw [localizedChoice_app]
  change (chosenLift T).comparison.hom.app s ≫ (Primitive.generators e' d').Q.map (𝟙 _) ≫
    (chosenLift T).comparison.inv.app s = 𝟙 _
  dsimp only [chosenLift, localizedFactorFunctor]
  simp

end ContextualComposition.Factorization.Endpoint
