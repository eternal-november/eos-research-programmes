module
public import ContextualComposition.TargetChange
@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor
universe vK vL vK' vL' vC uK uL uK' uL' uC
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'} {C : Type uC}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L'] [Category.{vC} C]
variable (e : K ⥤ C) (d : L ⥤ C) (e' : K' ⥤ C) (d' : L' ⥤ C)

/-- Actual endpoint lift data, with the source lift contravariant in extensions. -/
structure Data where
  input : K ⥤ K'
  output : L ⥤ L'
  inputLift : input ⋙ e' ⟶ e
  outputLift : d ⟶ output ⋙ d'

variable {e d e' d'}
/-- Transport retains the middle object and both actual native grade maps. -/
def factorFunctor (T : Data e d e' d') : Object e d ⥤ Object e' d' where
  obj s := ⟨s.middle, T.input.obj s.left, T.output.obj s.right,
    T.inputLift.app s.left ≫ s.first, s.second ≫ T.outputLift.app s.right⟩
  map {s t} f :=
    { left := T.input.map f.left
      middle := f.middle
      right := T.output.map f.right
      first_square := by
        rw [← Category.assoc, ← Functor.comp_map, T.inputLift.naturality,
          Category.assoc, f.first_square, Category.assoc]
      second_square := by
        rw [← Category.assoc, f.second_square, Category.assoc,
          T.outputLift.naturality, Category.assoc]
        rfl }
  map_id s := by
    apply Factorization.Hom.ext
    · exact T.input.map_id _
    · rfl
    · exact T.output.map_id _
  map_comp f g := by
    apply Factorization.Hom.ext
    · exact T.input.map_comp _ _
    · rfl
    · exact T.output.map_comp _ _

def commaFunctor (T : Data e d e' d') : Comma e d ⥤ Comma e' d' where
  obj s := ⟨T.input.obj s.left, T.output.obj s.right,
    T.inputLift.app s.left ≫ s.hom ≫ T.outputLift.app s.right⟩
  map {s t} f :=
    { left := T.input.map f.left
      right := T.output.map f.right
      w := by
        change e'.map (T.input.map f.left) ≫ (T.inputLift.app t.left ≫ t.hom ≫ T.outputLift.app t.right) =
          (T.inputLift.app s.left ≫ s.hom ≫ T.outputLift.app s.right) ≫ d'.map (T.output.map f.right)
        rw [← Category.assoc, ← Functor.comp_map, T.inputLift.naturality,
          Category.assoc, ← Category.assoc (e.map f.left), f.w, Category.assoc,
          T.outputLift.naturality]
        simp only [Functor.comp_map, Category.assoc] }
  map_id s := by apply Comma.hom_ext <;> apply Functor.map_id
  map_comp f g := by apply Comma.hom_ext <;> apply Functor.map_comp

/-- Normalization commutes with endpoint transport, preserving native grades. -/
def normalizationIso (T : Data e d e' d') :
    factorFunctor T ⋙ normalize e' d' ≅ normalize e d ⋙ commaFunctor T :=
  NatIso.ofComponents (fun s => Comma.isoMk (Iso.refl _) (Iso.refl _) (by
    simp [factorFunctor, normalize, commaFunctor, Category.assoc])) (by
    intro s t f
    apply Comma.hom_ext
    · change T.input.map f.left ≫ 𝟙 _ = 𝟙 _ ≫ T.input.map f.left; simp
    · change T.output.map f.right ≫ 𝟙 _ = 𝟙 _ ≫ T.output.map f.right; simp)

/-- The normalization section changes its splitting object by the source lift. -/
def sectionComparison (T : Data e d e' d') :
    commaFunctor T ⋙ sectionFunctor e' d' ⟶ sectionFunctor e d ⋙ factorFunctor T where
  app s :=
    { left := 𝟙 _
      middle := T.inputLift.app s.left
      right := 𝟙 _
      first_square := by simp [commaFunctor, sectionFunctor, factorFunctor]
      second_square := by simp [commaFunctor, sectionFunctor, factorFunctor] }
  naturality s t f := by
    apply Factorization.Hom.ext
    · change T.input.map f.left ≫ 𝟙 _ = 𝟙 _ ≫ T.input.map f.left; simp
    · exact T.inputLift.naturality f.left
    · change T.output.map f.right ≫ 𝟙 _ = 𝟙 _ ≫ T.output.map f.right; simp

/-- Section comparison need not be invertible before localization. -/
theorem sectionComparison_in_class (T : Data e d e' d') (s : Comma e d) :
    balanceClass e' d' ((sectionComparison T).app s) := by
  constructor <;> change IsIso (𝟙 _) <;> infer_instance

/-- It becomes invertible at the exact primitive localization. -/
noncomputable def localizedSectionComparison (T : Data e d e' d') :
    (commaFunctor T ⋙ sectionFunctor e' d') ⋙ (Primitive.generators e' d').Q ≅
      (sectionFunctor e d ⋙ factorFunctor T) ⋙ (Primitive.generators e' d').Q := by
  let a := whiskerRight (sectionComparison T) (Primitive.generators e' d').Q
  have : ∀ s, IsIso (a.app s) := fun s =>
    (Primitive.localized_iso_iff e' d' _).mpr (sectionComparison_in_class T s)
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a


/-- Transport respects the exact primitive localization, not just bodies. -/
theorem factor_inverts (T : Data e d e' d') :
    (Primitive.generators e d).IsInvertedBy (factorFunctor T ⋙ (Primitive.generators e' d').Q) := by
  intro s t f hf
  apply (Primitive.localized_iso_iff e' d' ((factorFunctor T).map f)).mpr
  obtain ⟨hl,hr⟩ := Primitive.generators_le e d _ hf
  let := hl
  let := hr
  constructor
  · exact T.input.map_isIso f.left
  · exact T.output.map_isIso f.right

noncomputable def localizedFactorFunctor (T : Data e d e' d') :
    (Primitive.generators e d).Localization ⥤ (Primitive.generators e' d').Localization :=
  Localization.lift (factorFunctor T ⋙ (Primitive.generators e' d').Q) (factor_inverts T)
    (Primitive.generators e d).Q

variable (e d)
def identityData : Data e d e d :=
  ⟨𝟭 K, 𝟭 L, (Functor.leftUnitor e).hom, (Functor.leftUnitor d).inv⟩
variable {e d}

def factorIdentityIso : factorFunctor (identityData e d) ≅ 𝟭 (Object e d) :=
  NatIso.ofComponents (fun s =>
    { hom := ⟨𝟙 _, 𝟙 _, 𝟙 _, by simp [identityData, factorFunctor], by simp [identityData, factorFunctor]⟩
      inv := ⟨𝟙 _, 𝟙 _, 𝟙 _, by simp [identityData, factorFunctor], by simp [identityData, factorFunctor]⟩
      hom_inv_id := by apply Factorization.Hom.ext <;> change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ <;> simp
      inv_hom_id := by apply Factorization.Hom.ext <;> change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ <;> simp }) (by
    intro s t f
    apply Factorization.Hom.ext
    · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left; simp
    · change f.middle ≫ 𝟙 _ = 𝟙 _ ≫ f.middle; simp
    · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right; simp)

universe vK'' vL'' uK'' uL''
variable {K'' : Type uK''} {L'' : Type uL''} [Category.{vK''} K''] [Category.{vL''} L'']
variable {e'' : K'' ⥤ C} {d'' : L'' ⥤ C}
/-- Composite lifts retain the ordinary functor associators. -/
def composeData (T : Data e d e' d') (U : Data e' d' e'' d'') : Data e d e'' d'' where
  input := T.input ⋙ U.input
  output := T.output ⋙ U.output
  inputLift := (Functor.associator T.input U.input e'').hom ≫
    whiskerLeft T.input U.inputLift ≫ T.inputLift
  outputLift := T.outputLift ≫ whiskerLeft T.output U.outputLift ≫
    (Functor.associator T.output U.output d'').inv

def factorCompositionIso (T : Data e d e' d') (U : Data e' d' e'' d'') :
    factorFunctor T ⋙ factorFunctor U ≅ factorFunctor (composeData T U) :=
  NatIso.ofComponents (fun s =>
    { hom := ⟨𝟙 _, 𝟙 _, 𝟙 _, by simp [factorFunctor, composeData, Category.assoc], by simp [factorFunctor, composeData, Category.assoc]⟩
      inv := ⟨𝟙 _, 𝟙 _, 𝟙 _, by simp [factorFunctor, composeData, Category.assoc], by simp [factorFunctor, composeData, Category.assoc]⟩
      hom_inv_id := by apply Factorization.Hom.ext <;> change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ <;> simp
      inv_hom_id := by apply Factorization.Hom.ext <;> change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ <;> simp }) (by
    intro s t f
    apply Factorization.Hom.ext
    · change U.input.map (T.input.map f.left) ≫ 𝟙 _ = 𝟙 _ ≫ U.input.map (T.input.map f.left); simp
    · change f.middle ≫ 𝟙 _ = 𝟙 _ ≫ f.middle; simp
    · change U.output.map (T.output.map f.right) ≫ 𝟙 _ = 𝟙 _ ≫ U.output.map (T.output.map f.right); simp)

def commaCompositionIso (T : Data e d e' d') (U : Data e' d' e'' d'') :
    commaFunctor T ⋙ commaFunctor U ≅ commaFunctor (composeData T U) :=
  NatIso.ofComponents (fun s => Comma.isoMk (Iso.refl _) (Iso.refl _)
    (by simp [commaFunctor, composeData, Category.assoc])) (by
    intro s t f
    apply Comma.hom_ext
    · change U.input.map (T.input.map f.left) ≫ 𝟙 _ = 𝟙 _ ≫ U.input.map (T.input.map f.left); simp
    · change U.output.map (T.output.map f.right) ≫ 𝟙 _ = 𝟙 _ ≫ U.output.map (T.output.map f.right); simp)

/-- The source-lift section comparison composes by the actual composite lift. -/
theorem section_composition (T : Data e d e' d') (U : Data e' d' e'' d'') (s : Comma e d) :
    (sectionComparison (composeData T U)).app s =
      (sectionFunctor e'' d'').map ((commaCompositionIso T U).inv.app s) ≫
      (sectionComparison U).app ((commaFunctor T).obj s) ≫
      (factorFunctor U).map ((sectionComparison T).app s) ≫
      (factorCompositionIso T U).hom.app ((sectionFunctor e d).obj s) := by
  apply Factorization.Hom.ext
  · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ U.input.map (𝟙 _) ≫ 𝟙 _; simp
  · change 𝟙 _ ≫ U.inputLift.app (T.input.obj s.left) ≫ T.inputLift.app s.left =
      e''.map (𝟙 _) ≫ U.inputLift.app (T.input.obj s.left) ≫ T.inputLift.app s.left ≫ 𝟙 _
    simp
  · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ U.output.map (𝟙 _) ≫ 𝟙 _; simp


def commaIdentityIso : commaFunctor (identityData e d) ≅ 𝟭 (Comma e d) :=
  NatIso.ofComponents (fun s => Comma.isoMk (Iso.refl _) (Iso.refl _)
    (by simp [commaFunctor, identityData])) (by
    intro s t f
    apply Comma.hom_ext
    · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left; simp
    · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right; simp)

theorem section_identity (s : Comma e d) :
    (sectionComparison (identityData e d)).app s ≫ factorIdentityIso.hom.app ((sectionFunctor e d).obj s) =
      (sectionFunctor e d).map (commaIdentityIso.hom.app s) := by
  apply Factorization.Hom.ext
  · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
  · change 𝟙 _ ≫ 𝟙 _ = e.map (𝟙 _); simp
  · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp

theorem normalization_composition (T : Data e d e' d') (U : Data e' d' e'' d'') (s : Object e d) :
    (normalizationIso (composeData T U)).hom.app s =
      (normalize e'' d'').map ((factorCompositionIso T U).inv.app s) ≫
      (normalizationIso U).hom.app ((factorFunctor T).obj s) ≫
      (commaFunctor U).map ((normalizationIso T).hom.app s) ≫
      (commaCompositionIso T U).hom.app ((normalize e d).obj s) := by
  apply Comma.hom_ext
  · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ U.input.map (𝟙 _) ≫ 𝟙 _; simp
  · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ U.output.map (𝟙 _) ≫ 𝟙 _; simp

/-- The section comparison is the particular primitive balance at the source lift. -/
theorem section_balance_target (T : Data e d e' d') (s : Comma e d) :
    (⟨e.obj s.left, T.input.obj s.left, T.output.obj s.right,
      𝟙 _ ≫ T.inputLift.app s.left, s.hom ≫ T.outputLift.app s.right⟩ : Object e' d') =
      (factorFunctor T).obj ((sectionFunctor e d).obj s) := by
  simp [factorFunctor, sectionFunctor]

theorem section_is_primitive (T : Data e d e' d') (s : Comma e d) :
    balance e' d' (T.input.obj s.left) (T.output.obj s.right) (𝟙 _)
      (T.inputLift.app s.left) (s.hom ≫ T.outputLift.app s.right) ≫
      eqToHom (section_balance_target T s) = (sectionComparison T).app s := by
  apply Factorization.Hom.ext
  · change 𝟙 _ ≫ (eqToHom (section_balance_target T s)).left = 𝟙 _
    rw [Primitive.eqToHom_left]; simp [factorFunctor, sectionFunctor]
  · change T.inputLift.app s.left ≫ (eqToHom (section_balance_target T s)).middle = T.inputLift.app s.left
    rw [Primitive.eqToHom_middle]; simp [factorFunctor, sectionFunctor]
  · change 𝟙 _ ≫ (eqToHom (section_balance_target T s)).right = 𝟙 _
    rw [Primitive.eqToHom_right]; simp [factorFunctor, sectionFunctor]

/-- Compatible changes of weak endpoint choices. Lift compatibility is explicit. -/
structure ChoiceIso (T U : Data e d e' d') where
  input : T.input ≅ U.input
  output : T.output ≅ U.output
  input_lift : ∀ P, e'.map (input.hom.app P) ≫ U.inputLift.app P = T.inputLift.app P
  output_lift : ∀ Q, T.outputLift.app Q ≫ d'.map (output.hom.app Q) = U.outputLift.app Q

namespace ChoiceIso
variable {T U : Data e d e' d'} (a : ChoiceIso T U)
theorem input_inv (P : K) : e'.map (a.input.inv.app P) ≫ T.inputLift.app P = U.inputLift.app P := by
  rw [← a.input_lift P, ← Category.assoc, ← e'.map_comp, a.input.inv_hom_id_app, e'.map_id, Category.id_comp]
theorem output_inv (Q : L) : U.outputLift.app Q ≫ d'.map (a.output.inv.app Q) = T.outputLift.app Q := by
  rw [← a.output_lift Q, Category.assoc, ← d'.map_comp, a.output.hom_inv_id_app, d'.map_id]
  exact Category.comp_id _

def factorIso : factorFunctor T ≅ factorFunctor U :=
  NatIso.ofComponents (fun s =>
    { hom :=
        { left := a.input.hom.app s.left
          middle := 𝟙 _
          right := a.output.hom.app s.right
          first_square := by
            change e'.map _ ≫ (U.inputLift.app s.left ≫ s.first) = (T.inputLift.app s.left ≫ s.first) ≫ 𝟙 _
            rw [← Category.assoc, a.input_lift, Category.comp_id]
          second_square := by
            change 𝟙 _ ≫ (s.second ≫ U.outputLift.app s.right) = (s.second ≫ T.outputLift.app s.right) ≫ d'.map _
            rw [Category.id_comp, Category.assoc, a.output_lift] }
      inv :=
        { left := a.input.inv.app s.left
          middle := 𝟙 _
          right := a.output.inv.app s.right
          first_square := by
            change e'.map _ ≫ (T.inputLift.app s.left ≫ s.first) = (U.inputLift.app s.left ≫ s.first) ≫ 𝟙 _
            rw [← Category.assoc, a.input_inv, Category.comp_id]
          second_square := by
            change 𝟙 _ ≫ (s.second ≫ T.outputLift.app s.right) = (s.second ≫ U.outputLift.app s.right) ≫ d'.map _
            rw [Category.id_comp, Category.assoc, a.output_inv] }
      hom_inv_id := by
        apply Factorization.Hom.ext
        · exact a.input.hom_inv_id_app _
        · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
        · exact a.output.hom_inv_id_app _
      inv_hom_id := by
        apply Factorization.Hom.ext
        · exact a.input.inv_hom_id_app _
        · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
        · exact a.output.inv_hom_id_app _ }) (by
    intro s t f
    apply Factorization.Hom.ext
    · exact a.input.hom.naturality f.left
    · change f.middle ≫ 𝟙 _ = 𝟙 _ ≫ f.middle; simp
    · exact a.output.hom.naturality f.right)

def commaIso : commaFunctor T ≅ commaFunctor U :=
  NatIso.ofComponents (fun s => Comma.isoMk (a.input.app s.left) (a.output.app s.right) (by
    change e'.map (a.input.hom.app s.left) ≫ (U.inputLift.app s.left ≫ s.hom ≫ U.outputLift.app s.right) =
      (T.inputLift.app s.left ≫ s.hom ≫ T.outputLift.app s.right) ≫ d'.map (a.output.hom.app s.right)
    rw [← Category.assoc, a.input_lift]
    simp only [Category.assoc, a.output_lift])) (by
    intro s t f
    apply Comma.hom_ext
    · exact a.input.hom.naturality f.left
    · exact a.output.hom.naturality f.right)

/-- The nonidentity splitting-object lift is compatible with weak choice changes. -/
theorem section_naturality (s : Comma e d) :
    (sectionFunctor e' d').map (a.commaIso.hom.app s) ≫ (sectionComparison U).app s =
      (sectionComparison T).app s ≫ a.factorIso.hom.app ((sectionFunctor e d).obj s) := by
  apply Factorization.Hom.ext
  · change a.input.hom.app s.left ≫ 𝟙 _ = 𝟙 _ ≫ a.input.hom.app s.left; simp
  · change e'.map (a.input.hom.app s.left) ≫ U.inputLift.app s.left = T.inputLift.app s.left ≫ 𝟙 _
    rw [a.input_lift, Category.comp_id]
  · change a.output.hom.app s.right ≫ 𝟙 _ = 𝟙 _ ≫ a.output.hom.app s.right; simp

theorem normalization_naturality (s : Object e d) :
    (normalize e' d').map (a.factorIso.hom.app s) ≫ (normalizationIso U).hom.app s =
      (normalizationIso T).hom.app s ≫ a.commaIso.hom.app ((normalize e d).obj s) := by
  apply Comma.hom_ext
  · change a.input.hom.app s.left ≫ 𝟙 _ = 𝟙 _ ≫ a.input.hom.app s.left; simp
  · change a.output.hom.app s.right ≫ 𝟙 _ = 𝟙 _ ≫ a.output.hom.app s.right; simp
end ChoiceIso


/-- The local comma equivalence has an actual square on primitive localizations. -/
noncomputable def localizedNormalizationIso (T : Data e d e' d') :
    localizedFactorFunctor T ⋙ Primitive.localizedNormalize e' d' ≅
      Primitive.localizedNormalize e d ⋙ commaFunctor T := by
  letI : Localization.Lifting (Primitive.generators e d).Q (Primitive.generators e d)
      (factorFunctor T ⋙ normalize e' d')
      (localizedFactorFunctor T ⋙ Primitive.localizedNormalize e' d') :=
    ⟨(Functor.associator (Primitive.generators e d).Q (localizedFactorFunctor T)
        (Primitive.localizedNormalize e' d')).symm ≪≫
      isoWhiskerRight (Localization.fac (factorFunctor T ⋙ (Primitive.generators e' d').Q)
        (factor_inverts T) (Primitive.generators e d).Q) (Primitive.localizedNormalize e' d') ≪≫
      Functor.associator (factorFunctor T) (Primitive.generators e' d').Q (Primitive.localizedNormalize e' d') ≪≫
      isoWhiskerLeft (factorFunctor T)
        (Localization.fac (normalize e' d') (Primitive.normalize_inverts e' d') (Primitive.generators e' d').Q)⟩
  letI : Localization.Lifting (Primitive.generators e d).Q (Primitive.generators e d)
      (normalize e d ⋙ commaFunctor T) (Primitive.localizedNormalize e d ⋙ commaFunctor T) := by
    dsimp [Primitive.localizedNormalize]
    infer_instance
  exact Localization.liftNatIso (Primitive.generators e d).Q (Primitive.generators e d)
    (factorFunctor T ⋙ normalize e' d') (normalize e d ⋙ commaFunctor T)
    (localizedFactorFunctor T ⋙ Primitive.localizedNormalize e' d')
    (Primitive.localizedNormalize e d ⋙ commaFunctor T) (normalizationIso T)

namespace ChoiceIso
variable {T U V : Data e d e' d'}
def refl (T : Data e d e' d') : ChoiceIso T T :=
  ⟨Iso.refl _, Iso.refl _, by intro P; simp, by intro Q; simp⟩
def trans (a : ChoiceIso T U) (b : ChoiceIso U V) : ChoiceIso T V where
  input := a.input ≪≫ b.input
  output := a.output ≪≫ b.output
  input_lift P := by
    change e'.map (a.input.hom.app P ≫ b.input.hom.app P) ≫ V.inputLift.app P = T.inputLift.app P
    rw [e'.map_comp, Category.assoc, b.input_lift, a.input_lift]
  output_lift Q := by
    change T.outputLift.app Q ≫ d'.map (a.output.hom.app Q ≫ b.output.hom.app Q) = V.outputLift.app Q
    rw [d'.map_comp, ← Category.assoc, a.output_lift, b.output_lift]

theorem factor_trans (a : ChoiceIso T U) (b : ChoiceIso U V) :
    (a.trans b).factorIso.hom = a.factorIso.hom ≫ b.factorIso.hom := by
  apply NatTrans.ext; funext s; apply Factorization.Hom.ext
  · rfl
  · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp
  · rfl

theorem comma_trans (a : ChoiceIso T U) (b : ChoiceIso U V) :
    (a.trans b).commaIso.hom = a.commaIso.hom ≫ b.commaIso.hom := by
  apply NatTrans.ext; funext s; apply Comma.hom_ext <;> rfl
end ChoiceIso

/-- Unit weak-choice comparisons are supplied by the ordinary grade-functor unitors. -/
def leftUnitChoice (T : Data e d e' d') : ChoiceIso (composeData (identityData e d) T) T :=
  ⟨Functor.leftUnitor T.input, Functor.leftUnitor T.output,
    by intro P; simp [composeData, identityData], by intro Q; simp [composeData, identityData]⟩
def rightUnitChoice (T : Data e d e' d') : ChoiceIso (composeData T (identityData e' d')) T :=
  ⟨Functor.rightUnitor T.input, Functor.rightUnitor T.output,
    by intro P; simp [composeData, identityData], by intro Q; simp [composeData, identityData]⟩

universe vK''' vL''' uK''' uL'''
variable {K''' : Type uK'''} {L''' : Type uL'''} [Category.{vK'''} K'''] [Category.{vL'''} L''']
variable {e''' : K''' ⥤ C} {d''' : L''' ⥤ C}
/-- Associator compatibility is derived from lift composition, not assumed. -/
def associatorChoice (T : Data e d e' d') (U : Data e' d' e'' d'') (V : Data e'' d'' e''' d''') :
    ChoiceIso (composeData (composeData T U) V) (composeData T (composeData U V)) :=
  ⟨Functor.associator T.input U.input V.input, Functor.associator T.output U.output V.output,
    by intro P; simp [composeData, Category.assoc], by intro Q; simp [composeData, Category.assoc]⟩

/-- Endpoint transport's associativity equation retains the weak-choice associator. -/
theorem factor_associativity (T : Data e d e' d') (U : Data e' d' e'' d'')
    (V : Data e'' d'' e''' d''') (s : Object e d) :
    (factorFunctor V).map ((factorCompositionIso T U).hom.app s) ≫
      (factorCompositionIso (composeData T U) V).hom.app s ≫
      (associatorChoice T U V).factorIso.hom.app s =
    (factorCompositionIso U V).hom.app ((factorFunctor T).obj s) ≫
      (factorCompositionIso T (composeData U V)).hom.app s := by
  apply Factorization.Hom.ext
  · change V.input.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp
  · change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp
  · change V.output.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp


theorem factor_left_unit (T : Data e d e' d') (s : Object e d) :
    (factorFunctor T).map (factorIdentityIso.hom.app s) =
      (factorCompositionIso (identityData e d) T).hom.app s ≫ (leftUnitChoice T).factorIso.hom.app s := by
  apply Factorization.Hom.ext
  · change T.input.map (𝟙 _) = 𝟙 _ ≫ 𝟙 _; simp
  · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp
  · change T.output.map (𝟙 _) = 𝟙 _ ≫ 𝟙 _; simp

theorem factor_right_unit (T : Data e d e' d') (s : Object e d) :
    factorIdentityIso.hom.app ((factorFunctor T).obj s) =
      (factorCompositionIso T (identityData e' d')).hom.app s ≫ (rightUnitChoice T).factorIso.hom.app s := by
  apply Factorization.Hom.ext <;> change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ <;> simp

theorem comma_left_unit (T : Data e d e' d') (s : Comma e d) :
    (commaFunctor T).map (commaIdentityIso.hom.app s) =
      (commaCompositionIso (identityData e d) T).hom.app s ≫ (leftUnitChoice T).commaIso.hom.app s := by
  apply Comma.hom_ext
  · change T.input.map (𝟙 _) = 𝟙 _ ≫ 𝟙 _; simp
  · change T.output.map (𝟙 _) = 𝟙 _ ≫ 𝟙 _; simp

theorem comma_right_unit (T : Data e d e' d') (s : Comma e d) :
    commaIdentityIso.hom.app ((commaFunctor T).obj s) =
      (commaCompositionIso T (identityData e' d')).hom.app s ≫ (rightUnitChoice T).commaIso.hom.app s := by
  apply Comma.hom_ext <;> change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ <;> simp

theorem comma_associativity (T : Data e d e' d') (U : Data e' d' e'' d'')
    (V : Data e'' d'' e''' d''') (s : Comma e d) :
    (commaFunctor V).map ((commaCompositionIso T U).hom.app s) ≫
      (commaCompositionIso (composeData T U) V).hom.app s ≫
      (associatorChoice T U V).commaIso.hom.app s =
    (commaCompositionIso U V).hom.app ((commaFunctor T).obj s) ≫
      (commaCompositionIso T (composeData U V)).hom.app s := by
  apply Comma.hom_ext
  · change V.input.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp
  · change V.output.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp

theorem normalization_identity (s : Object e d) :
    (normalize e d).map (factorIdentityIso.hom.app s) =
      (normalizationIso (identityData e d)).hom.app s ≫ commaIdentityIso.hom.app ((normalize e d).obj s) := by
  apply Comma.hom_ext <;> change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ <;> simp

end ContextualComposition.Factorization.Endpoint
