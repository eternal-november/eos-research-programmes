module
public import ContextualComposition.Factorization
@[expose] public section
namespace ContextualComposition.Factorization.Primitive
open CategoryTheory CategoryTheory.Functor
universe vK vL vC uK uL uC
variable {K : Type uK} {L : Type uL} {C : Type uC}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vC} C]
variable (e : K ⥤ C) (d : L ⥤ C)

/-- Indexing data for precisely the source's identity-grade middle balances. -/
structure Data where
  P : K
  Q : L
  Z : C
  Z' : C
  x : e.obj P ⟶ Z
  u : Z ⟶ Z'
  y : Z' ⟶ d.obj Q

def arrow (b : Data e d) := balance e d b.P b.Q b.x b.u b.y

def generators : MorphismProperty (Object e d) := MorphismProperty.ofHoms (arrow e d)

theorem generators_le : generators e d ≤ balanceClass e d := by
  intro s t f hf
  cases hf with
  | mk b => exact balance_in_class e d b.P b.Q b.x b.u b.y

theorem eqToHom_left {s t : Object e d} (h : s = t) :
    (eqToHom h).left = eqToHom (congrArg Object.left h) := by cases h; rfl

theorem eqToHom_middle {s t : Object e d} (h : s = t) :
    (eqToHom h).middle = eqToHom (congrArg Object.middle h) := by cases h; rfl

theorem eqToHom_right {s t : Object e d} (h : s = t) :
    (eqToHom h).right = eqToHom (congrArg Object.right h) := by cases h; rfl

def contractionData (s : Object e d) : Data e d :=
  ⟨s.left, s.right, e.obj s.left, s.middle, 𝟙 _, s.first, s.second⟩

theorem contraction_target (s : Object e d) :
    (⟨s.middle, s.left, s.right, 𝟙 _ ≫ s.first, s.second⟩ : Object e d) = s := by
  cases s
  simp

theorem contraction_factor (s : Object e d) :
    arrow e d (contractionData e d s) ≫ eqToHom (contraction_target e d s) =
      (contraction e d).app s := by
  apply Hom.ext
  · change (𝟙 _) ≫ (eqToHom (contraction_target e d s)).left = 𝟙 _
    rw [eqToHom_left]; simp
  · change s.first ≫ (eqToHom (contraction_target e d s)).middle = s.first
    rw [eqToHom_middle]; simp
  · change (𝟙 _) ≫ (eqToHom (contraction_target e d s)).right = 𝟙 _
    rw [eqToHom_right]; simp

theorem primitive_inverts_contractions {D : Type*} [Category D]
    (F : Object e d ⥤ D) (h : (generators e d).IsInvertedBy F) (s : Object e d) :
    IsIso (F.map ((contraction e d).app s)) := by
  rw [← contraction_factor]
  dsimp only [arrow, contractionData, normalize, sectionFunctor, Functor.comp_obj, Functor.id_obj]
  rw [F.map_comp]
  have hi : IsIso (F.map (arrow e d (contractionData e d s))) :=
    h _ (MorphismProperty.ofHoms.mk (contractionData e d s))
  dsimp only [arrow, contractionData] at hi
  let := hi
  infer_instance

theorem inversion_iff {D : Type*} [Category D] (F : Object e d ⥤ D) :
    (generators e d).IsInvertedBy F ↔ (balanceClass e d).IsInvertedBy F := by
  constructor
  · intro h
    exact inverts_of_contractions e d F (primitive_inverts_contractions e d F h)
  · intro h s t f hf
    exact h f (generators_le e d f hf)

theorem normalize_inverts : (generators e d).IsInvertedBy (normalize e d) :=
  (inversion_iff e d (normalize e d)).mpr (Factorization.normalize_inverts e d)

noncomputable def localizedNormalize : (generators e d).Localization ⥤ Comma e d :=
  Localization.lift (normalize e d) (normalize_inverts e d) (generators e d).Q

noncomputable def localizedSection : Comma e d ⥤ (generators e d).Localization :=
  sectionFunctor e d ⋙ (generators e d).Q

noncomputable def localizedContraction :
    (normalize e d ⋙ sectionFunctor e d) ⋙ (generators e d).Q ≅
      𝟭 (Object e d) ⋙ (generators e d).Q := by
  let n := whiskerRight (contraction e d) (generators e d).Q
  have : ∀ s, IsIso (n.app s) := fun s =>
    primitive_inverts_contractions e d (generators e d).Q
      (Localization.inverts (generators e d).Q (generators e d)) s
  have : IsIso n := NatIso.isIso_of_isIso_app n
  exact asIso n

/-- Localization at exactly the primitive identity-grade middle balances.
The full structured pseudobalanced-cocone comparison is a separate interface. -/
noncomputable def localizationEquivalence :
    (generators e d).Localization ≌ Comma e d := by
  letI : Localization.Lifting (generators e d).Q (generators e d)
      (normalize e d ⋙ sectionFunctor e d ⋙ (generators e d).Q)
      (localizedNormalize e d ⋙ localizedSection e d) := by
    dsimp [localizedNormalize, localizedSection]
    infer_instance
  exact CategoryTheory.Equivalence.mk (localizedNormalize e d) (localizedSection e d)
    (Localization.liftNatIso (generators e d).Q (generators e d)
      (generators e d).Q (normalize e d ⋙ sectionFunctor e d ⋙ (generators e d).Q)
      (𝟭 _) (localizedNormalize e d ⋙ localizedSection e d)
      ((Functor.leftUnitor _).symm ≪≫ (localizedContraction e d).symm ≪≫
        Functor.associator _ _ _))
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (sectionFunctor e d)
        (Localization.fac (normalize e d) (normalize_inverts e d) (generators e d).Q) ≪≫
      sectionIso e d)

noncomputable instance normalizationIsLocalization :
    (normalize e d).IsLocalization (generators e d) :=
  Functor.IsLocalization.of_equivalence_target (generators e d).Q (generators e d)
    (normalize e d) (localizationEquivalence e d)
    (Localization.fac (normalize e d) (normalize_inverts e d) (generators e d).Q)

noncomputable def universalProperty (D : Type*) [Category D] :
    (Comma e d ⥤ D) ≌ (generators e d).FunctorsInverting D :=
  Localization.functorEquivalence (normalize e d) (generators e d) D

theorem localized_iso_iff {s t : Object e d} (f : s ⟶ t) :
    IsIso ((generators e d).Q.map f) ↔ balanceClass e d f := by
  constructor
  · intro h
    let := h
    have h' : IsIso (((generators e d).Q ⋙ localizedNormalize e d).map f) :=
      (localizedNormalize e d).map_isIso ((generators e d).Q.map f)
    have hn := (NatIso.isIso_map_iff
      (Localization.fac (normalize e d) (normalize_inverts e d) (generators e d).Q) f).mp h'
    exact (Factorization.normalize_iso_iff e d f).mp hn
  · exact (inversion_iff e d (generators e d).Q).mp
      (Localization.inverts (generators e d).Q (generators e d)) f

noncomputable def sectionFullyFaithful : (localizedSection e d).FullyFaithful :=
  (localizationEquivalence e d).fullyFaithfulInverse

theorem native_map_injective {s t : Comma e d} (f g : s ⟶ t)
    (h : (localizedSection e d).map f = (localizedSection e d).map g) : f = g :=
  (sectionFullyFaithful e d).faithful.map_injective h

noncomputable def localizationComparison :
    (generators e d).Localization ≌ (balanceClass e d).Localization :=
  (localizationEquivalence e d).trans (Factorization.localizationEquivalence e d).symm

def afterOutput {s t : Object e d} (f : s ⟶ t) : Object e d :=
  ⟨s.middle, s.left, t.right, s.first, f.middle ≫ t.second⟩

def afterBalance {s t : Object e d} (f : s ⟶ t) : Object e d :=
  ⟨t.middle, s.left, t.right, s.first ≫ f.middle, t.second⟩

/-- Native output-grade update at a fixed middle object. -/
def outputUpdate {s t : Object e d} (f : s ⟶ t) : s ⟶ afterOutput e d f :=
  { left := 𝟙 _
    middle := 𝟙 _
    right := f.right
    first_square := by simp [afterOutput]
    second_square := by simpa [afterOutput] using f.second_square }

/-- Native input-grade update at a fixed middle object. -/
def inputUpdate {s t : Object e d} (f : s ⟶ t) : afterBalance e d f ⟶ t :=
  { left := f.left
    middle := 𝟙 _
    right := 𝟙 _
    first_square := by simpa [afterBalance] using f.first_square
    second_square := by simp [afterBalance] }

theorem arrow_decomposition {s t : Object e d} (f : s ⟶ t) :
    (outputUpdate e d f ≫ balance e d s.left t.right s.first f.middle t.second) ≫
      inputUpdate e d f = f := by
  apply Hom.ext
  · change ((𝟙 _) ≫ (𝟙 _)) ≫ f.left = f.left; simp
  · change ((𝟙 _) ≫ f.middle) ≫ (𝟙 _) = f.middle; simp
  · change (f.right ≫ (𝟙 _)) ≫ (𝟙 _) = f.right; simp

theorem outputUpdate_middle {s t : Object e d} (f : s ⟶ t) :
    (outputUpdate e d f).middle = 𝟙 s.middle := rfl

theorem inputUpdate_middle {s t : Object e d} (f : s ⟶ t) :
    (inputUpdate e d f).middle = 𝟙 t.middle := rfl

section Transformations
variable {D : Type*} [Category D] (F G : Object e d ⥤ D)
    (a : ∀ s, F.obj s ⟶ G.obj s)

def NaturalOn {s t : Object e d} (f : s ⟶ t) : Prop :=
  F.map f ≫ a t = a s ≫ G.map f

theorem naturalOn_comp {s t u : Object e d} {f : s ⟶ t} {g : t ⟶ u}
    (hf : NaturalOn e d F G a f) (hg : NaturalOn e d F G a g) :
    NaturalOn e d F G a (f ≫ g) := by
  dsimp [NaturalOn] at *
  rw [F.map_comp, G.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

/-- Checking transformations on the two native updates and primitive balances
suffices on every factorization arrow; no extra middle arrows are omitted. -/
def transformationOfGenerators
    (hout : ∀ {s t} (f : s ⟶ t), NaturalOn e d F G a (outputUpdate e d f))
    (hin : ∀ {s t} (f : s ⟶ t), NaturalOn e d F G a (inputUpdate e d f))
    (hbal : ∀ b : Data e d, NaturalOn e d F G a (arrow e d b)) : F ⟶ G where
  app := a
  naturality s t f := by
    change NaturalOn e d F G a f
    rw [← arrow_decomposition e d f]
    exact naturalOn_comp e d F G a
      (naturalOn_comp e d F G a (hout f)
        (hbal ⟨s.left, t.right, s.middle, t.middle, s.first, f.middle, t.second⟩)) (hin f)
end Transformations

end ContextualComposition.Factorization.Primitive
