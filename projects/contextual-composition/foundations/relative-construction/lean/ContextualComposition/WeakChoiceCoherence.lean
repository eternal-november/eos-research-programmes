module
public import ContextualComposition.LocalizationDescent
@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor
universe vK vL vK' vL' vK'' vL'' vC uK uL uK' uL' uK'' uL'' uC
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
variable {K'' : Type uK''} {L'' : Type uL''} {C : Type uC}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L']
variable [Category.{vK''} K''] [Category.{vL''} L''] [Category.{vC} C]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}
variable {e'' : K'' ⥤ C} {d'' : L'' ⥤ C}
namespace ChoiceIso
@[ext] theorem ext {T U : Data e d e' d'} {a b : ChoiceIso T U}
    (hi : a.input = b.input) (ho : a.output = b.output) : a = b := by
  cases a; cases b; cases hi; cases ho; rfl

/-- Left whiskering derives lift compatibility at the actual transported grades. -/
def whiskerLeft (T : Data e d e' d') {U V : Data e' d' e'' d''} (b : ChoiceIso U V) :
    ChoiceIso (composeData T U) (composeData T V) where
  input := isoWhiskerLeft T.input b.input
  output := isoWhiskerLeft T.output b.output
  input_lift P := by
    change e''.map (b.input.hom.app (T.input.obj P)) ≫ (𝟙 _ ≫ V.inputLift.app (T.input.obj P) ≫ T.inputLift.app P) =
      𝟙 _ ≫ U.inputLift.app (T.input.obj P) ≫ T.inputLift.app P
    simp only [Category.id_comp]
    rw [← Category.assoc, b.input_lift]
  output_lift Q := by
    change (T.outputLift.app Q ≫ U.outputLift.app (T.output.obj Q) ≫ 𝟙 _) ≫ d''.map (b.output.hom.app (T.output.obj Q)) =
      T.outputLift.app Q ≫ V.outputLift.app (T.output.obj Q) ≫ 𝟙 _
    simp only [Category.comp_id]
    rw [Category.assoc, b.output_lift]

/-- Right whiskering uses naturality of the second endpoint's lifts. -/
def whiskerRight {T U : Data e d e' d'} (a : ChoiceIso T U) (V : Data e' d' e'' d'') :
    ChoiceIso (composeData T V) (composeData U V) where
  input := isoWhiskerRight a.input V.input
  output := isoWhiskerRight a.output V.output
  input_lift P := by
    change e''.map (V.input.map (a.input.hom.app P)) ≫ (𝟙 _ ≫ V.inputLift.app (U.input.obj P) ≫ U.inputLift.app P) =
      𝟙 _ ≫ V.inputLift.app (T.input.obj P) ≫ T.inputLift.app P
    simp only [Category.id_comp]
    rw [← Category.assoc, ← Functor.comp_map, V.inputLift.naturality, Category.assoc, a.input_lift]
  output_lift Q := by
    change (T.outputLift.app Q ≫ V.outputLift.app (T.output.obj Q) ≫ 𝟙 _) ≫
      d''.map (V.output.map (a.output.hom.app Q)) = U.outputLift.app Q ≫ V.outputLift.app (U.output.obj Q) ≫ 𝟙 _
    simp only [Category.comp_id]
    rw [Category.assoc, ← Functor.comp_map, ← V.outputLift.naturality, ← Category.assoc, a.output_lift]

def horizontal {T U : Data e d e' d'} {V W : Data e' d' e'' d''}
    (a : ChoiceIso T U) (b : ChoiceIso V W) : ChoiceIso (composeData T V) (composeData U W) :=
  (a.whiskerRight V).trans (whiskerLeft U b)

/-- The two actual native-map routes defining horizontal composition agree. -/
theorem horizontal_interchange {T U : Data e d e' d'} {V W : Data e' d' e'' d''}
    (a : ChoiceIso T U) (b : ChoiceIso V W) :
    a.horizontal b = (whiskerLeft T b).trans (a.whiskerRight W) := by
  apply ext
  · apply Iso.ext; apply NatTrans.ext; funext P
    exact b.input.hom.naturality (a.input.hom.app P)
  · apply Iso.ext; apply NatTrans.ext; funext Q
    exact b.output.hom.naturality (a.output.hom.app Q)

/-- Factor comparisons are natural in right-whiskered choices on actual maps. -/
theorem factor_whiskerRight {T U : Data e d e' d'} (a : ChoiceIso T U) (V : Data e' d' e'' d'')
    (s : Object e d) :
    (factorCompositionIso T V).hom.app s ≫ (a.whiskerRight V).factorIso.hom.app s =
      (factorFunctor V).map (a.factorIso.hom.app s) ≫ (factorCompositionIso U V).hom.app s := by
  apply Factorization.Hom.ext
  · change 𝟙 _ ≫ V.input.map (a.input.hom.app s.left) = V.input.map (a.input.hom.app s.left) ≫ 𝟙 _; simp
  · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _; rfl
  · change 𝟙 _ ≫ V.output.map (a.output.hom.app s.right) = V.output.map (a.output.hom.app s.right) ≫ 𝟙 _; simp

theorem factor_whiskerLeft (T : Data e d e' d') {U V : Data e' d' e'' d''} (b : ChoiceIso U V)
    (s : Object e d) :
    (factorCompositionIso T U).hom.app s ≫ (whiskerLeft T b).factorIso.hom.app s =
      b.factorIso.hom.app ((factorFunctor T).obj s) ≫ (factorCompositionIso T V).hom.app s := by
  apply Factorization.Hom.ext
  · change 𝟙 _ ≫ b.input.hom.app (T.input.obj s.left) = b.input.hom.app (T.input.obj s.left) ≫ 𝟙 _; simp
  · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _; rfl
  · change 𝟙 _ ≫ b.output.hom.app (T.output.obj s.right) = b.output.hom.app (T.output.obj s.right) ≫ 𝟙 _; simp


theorem horizontal_identity (T : Data e d e' d') (U : Data e' d' e'' d'') :
    (refl T).horizontal (refl U) = refl (composeData T U) := by
  apply ext
  · apply Iso.ext; apply NatTrans.ext; funext P
    change U.input.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _; simp
  · apply Iso.ext; apply NatTrans.ext; funext Q
    change U.output.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _; simp

theorem horizontal_vertical {T U V : Data e d e' d'} {R S N : Data e' d' e'' d''}
    (a : ChoiceIso T U) (b : ChoiceIso U V) (c : ChoiceIso R S) (f : ChoiceIso S N) :
    (a.trans b).horizontal (c.trans f) = (a.horizontal c).trans (b.horizontal f) := by
  apply ext
  · apply Iso.ext; apply NatTrans.ext; funext P
    change R.input.map (a.input.hom.app P ≫ b.input.hom.app P) ≫
      (c.input.hom.app (V.input.obj P) ≫ f.input.hom.app (V.input.obj P)) =
      (R.input.map (a.input.hom.app P) ≫ c.input.hom.app (U.input.obj P)) ≫
      (S.input.map (b.input.hom.app P) ≫ f.input.hom.app (V.input.obj P))
    rw [R.input.map_comp]
    simp only [Category.assoc]
    rw [c.input.hom.naturality_assoc]
  · apply Iso.ext; apply NatTrans.ext; funext Q
    change R.output.map (a.output.hom.app Q ≫ b.output.hom.app Q) ≫
      (c.output.hom.app (V.output.obj Q) ≫ f.output.hom.app (V.output.obj Q)) =
      (R.output.map (a.output.hom.app Q) ≫ c.output.hom.app (U.output.obj Q)) ≫
      (S.output.map (b.output.hom.app Q) ≫ f.output.hom.app (V.output.obj Q))
    rw [R.output.map_comp]
    simp only [Category.assoc]
    rw [c.output.hom.naturality_assoc]
end ChoiceIso

universe vK''' vL''' vK'''' vL'''' uK''' uL''' uK'''' uL''''
variable {K''' : Type uK'''} {L''' : Type uL'''} {K'''' : Type uK''''} {L'''' : Type uL''''}
variable [Category.{vK'''} K'''] [Category.{vL'''} L'''] [Category.{vK''''} K''''] [Category.{vL''''} L'''']
variable {e''' : K''' ⥤ C} {d''' : L''' ⥤ C} {e'''' : K'''' ⥤ C} {d'''' : L'''' ⥤ C}

/-- Pentagon of the actual lift-compatible endpoint associator choices. -/
theorem choice_pentagon (T : Data e d e' d') (U : Data e' d' e'' d'')
    (V : Data e'' d'' e''' d''') (W : Data e''' d''' e'''' d'''') :
    (associatorChoice (composeData T U) V W).trans (associatorChoice T U (composeData V W)) =
      ((associatorChoice T U V).whiskerRight W).trans
        ((associatorChoice T (composeData U V) W).trans (ChoiceIso.whiskerLeft T (associatorChoice U V W))) := by
  apply ChoiceIso.ext
  · apply Iso.ext; apply NatTrans.ext; funext P
    change 𝟙 _ ≫ 𝟙 _ = W.input.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _; simp
  · apply Iso.ext; apply NatTrans.ext; funext Q
    change 𝟙 _ ≫ 𝟙 _ = W.output.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _; simp

/-- Triangle compares source unit choices with the source associator, including whiskering. -/
theorem choice_triangle (T : Data e d e' d') (U : Data e' d' e'' d'') :
    (associatorChoice T (identityData e' d') U).trans (ChoiceIso.whiskerLeft T (leftUnitChoice U)) =
      (rightUnitChoice T).whiskerRight U := by
  apply ChoiceIso.ext
  · apply Iso.ext; apply NatTrans.ext; funext P
    change 𝟙 _ ≫ 𝟙 _ = U.input.map (𝟙 _); simp
  · apply Iso.ext; apply NatTrans.ext; funext Q
    change 𝟙 _ ≫ 𝟙 _ = U.output.map (𝟙 _); simp

/-- The concrete endpoint pentagon descends to the selected localized transport functors. -/
theorem localized_choice_pentagon (T : Data e d e' d') (U : Data e' d' e'' d'')
    (V : Data e'' d'' e''' d''') (W : Data e''' d''' e'''' d'''') :
    (localizedChoiceIso (associatorChoice (composeData T U) V W)).hom ≫
      (localizedChoiceIso (associatorChoice T U (composeData V W))).hom =
    (localizedChoiceIso ((associatorChoice T U V).whiskerRight W)).hom ≫
      (localizedChoiceIso (associatorChoice T (composeData U V) W)).hom ≫
      (localizedChoiceIso (ChoiceIso.whiskerLeft T (associatorChoice U V W))).hom := by
  rw [← localized_choice_composition, ← localized_choice_composition, ← localized_choice_composition, choice_pentagon]

theorem localized_choice_triangle (T : Data e d e' d') (U : Data e' d' e'' d'') :
    (localizedChoiceIso (associatorChoice T (identityData e' d') U)).hom ≫
      (localizedChoiceIso (ChoiceIso.whiskerLeft T (leftUnitChoice U))).hom =
      (localizedChoiceIso ((rightUnitChoice T).whiskerRight U)).hom := by
  rw [← localized_choice_composition, choice_triangle]



set_option backward.isDefEq.respectTransparency false in
theorem localized_composition_right_naturality {T U : Data e d e' d'} (a : ChoiceIso T U)
    (V : Data e' d' e'' d'') :
    (localizedCompositionIso T V).hom ≫ (localizedChoiceIso (a.whiskerRight V)).hom =
      CategoryTheory.Functor.whiskerRight (localizedChoiceIso a).hom (localizedFactorFunctor V) ≫
        (localizedCompositionIso U V).hom := by
  apply Descent.ext (Q := (Primitive.generators e d).Q) (W := Primitive.generators e d)
  intro s
  simp only [NatTrans.comp_app, whiskerRight_app, localizedComposition_app, localizedChoice_app]
  dsimp only [chosenLift, localizedFactorFunctor]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [((localizedFactorFunctor V).mapIso ((chosenLift U).comparison.app s)).inv_hom_id_assoc]
  have h := congrArg ((Primitive.generators e'' d'').Q.map) (a.factor_whiskerRight V s)
  simp only [Functor.map_comp] at h
  erw [← Category.assoc ((Primitive.generators e'' d'').Q.map ((factorCompositionIso T V).hom.app s)), h]
  simp only [Category.assoc]
  erw [← (chosenLift V).comparison.hom.naturality_assoc (a.factorIso.hom.app s)]
  dsimp only [chosenLift, localizedFactorFunctor, Functor.comp_map]

set_option backward.isDefEq.respectTransparency false in
theorem localized_composition_left_naturality (T : Data e d e' d') {U V : Data e' d' e'' d''}
    (b : ChoiceIso U V) :
    (localizedCompositionIso T U).hom ≫ (localizedChoiceIso (ChoiceIso.whiskerLeft T b)).hom =
      CategoryTheory.Functor.whiskerLeft (localizedFactorFunctor T) (localizedChoiceIso b).hom ≫
        (localizedCompositionIso T V).hom := by
  apply Descent.ext (Q := (Primitive.generators e d).Q) (W := Primitive.generators e d)
  intro s
  simp only [NatTrans.comp_app, whiskerLeft_app, localizedComposition_app, localizedChoice_app]
  dsimp only [chosenLift, localizedFactorFunctor]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [← (localizedChoiceIso b).hom.naturality_assoc ((chosenLift T).comparison.hom.app s)]
  erw [localizedChoice_app]
  dsimp only [chosenLift, localizedFactorFunctor]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have h := congrArg ((Primitive.generators e'' d'').Q.map) (ChoiceIso.factor_whiskerLeft T b s)
  simp only [Functor.map_comp] at h
  erw [← Category.assoc ((Primitive.generators e'' d'').Q.map ((factorCompositionIso T U).hom.app s)), h]
  simp only [Category.assoc]



theorem localized_horizontal_naturality {T U : Data e d e' d'} {V W : Data e' d' e'' d''}
    (a : ChoiceIso T U) (b : ChoiceIso V W) :
    (localizedCompositionIso T V).hom ≫ (localizedChoiceIso (a.horizontal b)).hom =
      CategoryTheory.Functor.whiskerRight (localizedChoiceIso a).hom (localizedFactorFunctor V) ≫
      CategoryTheory.Functor.whiskerLeft (localizedFactorFunctor U) (localizedChoiceIso b).hom ≫
      (localizedCompositionIso U W).hom := by
  change (localizedCompositionIso T V).hom ≫
    (localizedChoiceIso ((a.whiskerRight V).trans (ChoiceIso.whiskerLeft U b))).hom = _
  rw [localized_choice_composition, ← Category.assoc, localized_composition_right_naturality,
    Category.assoc, localized_composition_left_naturality]

/-- Naturality of the endpoint associator choice in all three actual choice maps. -/
theorem choice_associator_naturality {T T' : Data e d e' d'} {U U' : Data e' d' e'' d''}
    {V V' : Data e'' d'' e''' d'''} (a : ChoiceIso T T') (b : ChoiceIso U U') (c : ChoiceIso V V') :
    (associatorChoice T U V).trans (a.horizontal (b.horizontal c)) =
      ((a.horizontal b).horizontal c).trans (associatorChoice T' U' V') := by
  apply ChoiceIso.ext
  · apply Iso.ext; apply NatTrans.ext; funext P
    change 𝟙 _ ≫ (V.input.map (U.input.map (a.input.hom.app P)) ≫
      (V.input.map (b.input.hom.app (T'.input.obj P)) ≫ c.input.hom.app (U'.input.obj (T'.input.obj P)))) =
      (V.input.map (U.input.map (a.input.hom.app P) ≫ b.input.hom.app (T'.input.obj P)) ≫
        c.input.hom.app (U'.input.obj (T'.input.obj P))) ≫ 𝟙 _
    simp [Functor.map_comp, Category.assoc]
  · apply Iso.ext; apply NatTrans.ext; funext Q
    change 𝟙 _ ≫ (V.output.map (U.output.map (a.output.hom.app Q)) ≫
      (V.output.map (b.output.hom.app (T'.output.obj Q)) ≫ c.output.hom.app (U'.output.obj (T'.output.obj Q)))) =
      (V.output.map (U.output.map (a.output.hom.app Q) ≫ b.output.hom.app (T'.output.obj Q)) ≫
        c.output.hom.app (U'.output.obj (T'.output.obj Q))) ≫ 𝟙 _
    simp [Functor.map_comp, Category.assoc]

theorem choice_left_unit_naturality {T U : Data e d e' d'} (a : ChoiceIso T U) :
    (leftUnitChoice T).trans a = (ChoiceIso.whiskerLeft (identityData e d) a).trans (leftUnitChoice U) := by
  apply ChoiceIso.ext
  · apply Iso.ext; apply NatTrans.ext; funext P
    change 𝟙 _ ≫ a.input.hom.app P = a.input.hom.app P ≫ 𝟙 _; simp
  · apply Iso.ext; apply NatTrans.ext; funext Q
    change 𝟙 _ ≫ a.output.hom.app Q = a.output.hom.app Q ≫ 𝟙 _; simp

theorem choice_right_unit_naturality {T U : Data e d e' d'} (a : ChoiceIso T U) :
    (rightUnitChoice T).trans a = (a.whiskerRight (identityData e' d')).trans (rightUnitChoice U) := by
  apply ChoiceIso.ext
  · apply Iso.ext; apply NatTrans.ext; funext P
    change 𝟙 _ ≫ a.input.hom.app P = a.input.hom.app P ≫ 𝟙 _; simp
  · apply Iso.ext; apply NatTrans.ext; funext Q
    change 𝟙 _ ≫ a.output.hom.app Q = a.output.hom.app Q ≫ 𝟙 _; simp

end ContextualComposition.Factorization.Endpoint
