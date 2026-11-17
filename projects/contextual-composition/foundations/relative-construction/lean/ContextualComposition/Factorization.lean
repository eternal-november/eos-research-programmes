module
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Localization.Predicate
@[expose] public section
namespace ContextualComposition.Factorization
open CategoryTheory CategoryTheory.Functor
universe vK vL vC uK uL uC
variable {K : Type uK} {L : Type uL} {C : Type uC}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vC} C]
variable (e : K ⥤ C) (d : L ⥤ C)

/-- An actual two-step factorization, with both native grades retained. -/
structure Object where
  middle : C
  left : K
  right : L
  first : e.obj left ⟶ middle
  second : middle ⟶ d.obj right

@[ext]
structure Hom (s t : Object e d) where
  left : s.left ⟶ t.left
  middle : s.middle ⟶ t.middle
  right : s.right ⟶ t.right
  first_square : e.map left ≫ t.first = s.first ≫ middle
  second_square : middle ≫ t.second = s.second ≫ d.map right

attribute [reassoc] Hom.first_square Hom.second_square

instance category : Category (Object e d) where
  Hom := Hom e d
  id s := ⟨𝟙 _, 𝟙 _, 𝟙 _, by simp, by simp⟩
  comp f g :=
    { left := f.left ≫ g.left
      middle := f.middle ≫ g.middle
      right := f.right ≫ g.right
      first_square := by
        rw [Functor.map_comp, Category.assoc, g.first_square, ← Category.assoc,
          f.first_square, Category.assoc]
      second_square := by
        rw [Category.assoc, g.second_square, ← Category.assoc, f.second_square,
          Functor.map_comp, Category.assoc] }
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp [Category.assoc]

def normalize : Object e d ⥤ Comma e d where
  obj s := ⟨s.left, s.right, s.first ≫ s.second⟩
  map f :=
    { left := f.left
      right := f.right
      w := by
        rw [← Category.assoc, f.first_square, Category.assoc, f.second_square,
          Category.assoc] }

def sectionFunctor : Comma e d ⥤ Object e d where
  obj s := ⟨e.obj s.left, s.left, s.right, 𝟙 _, s.hom⟩
  map f :=
    { left := f.left
      middle := e.map f.left
      right := f.right
      first_square := by simp
      second_square := f.w }

def contraction : normalize e d ⋙ sectionFunctor e d ⟶ 𝟭 (Object e d) where
  app s :=
    { left := 𝟙 _
      middle := s.first
      right := 𝟙 _
      first_square := by simp [normalize, sectionFunctor]
      second_square := by simp [normalize, sectionFunctor] }
  naturality s t f := by
    apply Hom.ext
    · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left; simp
    · exact f.first_square
    · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right; simp

def sectionIso : sectionFunctor e d ⋙ normalize e d ≅ 𝟭 (Comma e d) :=
  NatIso.ofComponents (fun s => Comma.isoMk (Iso.refl _) (Iso.refl _) (by simp [normalize, sectionFunctor])) (by
    intro s t f
    apply Comma.hom_ext
    · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left; simp
    · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right; simp)

/-- Middle-object transport may be inverted, but arbitrary native grade maps may not. -/
def balanceClass : MorphismProperty (Object e d) :=
  fun _ _ f => IsIso f.left ∧ IsIso f.right

theorem normalize_inverts : (balanceClass e d).IsInvertedBy (normalize e d) := by
  intro s t f hf
  let : IsIso f.left := hf.1
  let : IsIso f.right := hf.2
  let il : s.left ≅ t.left := asIso f.left
  let ir : s.right ≅ t.right := asIso f.right
  let i : (normalize e d).obj s ≅ (normalize e d).obj t :=
    Comma.isoMk il ir ((normalize e d).map f).w
  have hi : i.hom = (normalize e d).map f := rfl
  rw [← hi]
  infer_instance

theorem contraction_in_class (s : Object e d) :
    balanceClass e d ((contraction e d).app s) := by
  constructor <;> change IsIso (𝟙 _) <;> infer_instance

noncomputable def localizedNormalize : (balanceClass e d).Localization ⥤ Comma e d :=
  Localization.lift (normalize e d) (normalize_inverts e d) (balanceClass e d).Q

noncomputable def localizedSection : Comma e d ⥤ (balanceClass e d).Localization :=
  sectionFunctor e d ⋙ (balanceClass e d).Q

noncomputable def localizedContraction :
    (normalize e d ⋙ sectionFunctor e d) ⋙ (balanceClass e d).Q ≅
      𝟭 (Object e d) ⋙ (balanceClass e d).Q := by
  let n := whiskerRight (contraction e d) (balanceClass e d).Q
  have : ∀ s, IsIso (n.app s) := fun s =>
    Localization.inverts (balanceClass e d).Q (balanceClass e d) _ (contraction_in_class e d s)
  have : IsIso n := NatIso.isIso_of_isIso_app n
  exact asIso n

/-- A genuine localization equivalence for arbitrary native grade categories.
Identification with a chosen pseudobalanced-coend presentation is separate. -/
noncomputable def localizationEquivalence :
    (balanceClass e d).Localization ≌ Comma e d := by
  letI : Localization.Lifting (balanceClass e d).Q (balanceClass e d)
      (normalize e d ⋙ sectionFunctor e d ⋙ (balanceClass e d).Q)
      (localizedNormalize e d ⋙ localizedSection e d) := by
    dsimp [localizedNormalize, localizedSection]
    infer_instance
  exact CategoryTheory.Equivalence.mk (localizedNormalize e d) (localizedSection e d)
    (Localization.liftNatIso (balanceClass e d).Q (balanceClass e d)
      (balanceClass e d).Q (normalize e d ⋙ sectionFunctor e d ⋙ (balanceClass e d).Q)
      (𝟭 _) (localizedNormalize e d ⋙ localizedSection e d)
      ((Functor.leftUnitor _).symm ≪≫ (localizedContraction e d).symm ≪≫
        Functor.associator _ _ _))
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (sectionFunctor e d)
        (Localization.fac (normalize e d) (normalize_inverts e d) (balanceClass e d).Q) ≪≫
      sectionIso e d)

theorem normalize_iso_iff {s t : Object e d} (f : s ⟶ t) :
    IsIso ((normalize e d).map f) ↔ balanceClass e d f := by
  constructor
  · intro h
    let := h
    constructor
    · exact (Comma.fst e d).map_isIso ((normalize e d).map f)
    · exact (Comma.snd e d).map_isIso ((normalize e d).map f)
  · exact normalize_inverts e d f

/-- The normalization functor satisfies the category-level localization
universal property; its proof uses the derived equivalence above. -/
noncomputable instance normalizationIsLocalization :
    (normalize e d).IsLocalization (balanceClass e d) :=
  Functor.IsLocalization.of_equivalence_target (balanceClass e d).Q (balanceClass e d)
    (normalize e d) (localizationEquivalence e d)
    (Localization.fac (normalize e d) (normalize_inverts e d) (balanceClass e d).Q)

theorem localized_iso_iff {s t : Object e d} (f : s ⟶ t) :
    IsIso ((balanceClass e d).Q.map f) ↔ balanceClass e d f := by
  constructor
  · intro h
    let := h
    have h' : IsIso (((balanceClass e d).Q ⋙ localizedNormalize e d).map f) :=
      (localizedNormalize e d).map_isIso ((balanceClass e d).Q.map f)
    have hn := (NatIso.isIso_map_iff
      (Localization.fac (normalize e d) (normalize_inverts e d) (balanceClass e d).Q) f).mp h'
    exact (normalize_iso_iff e d f).mp hn
  · exact Localization.inverts (balanceClass e d).Q (balanceClass e d) f

/-- The source's pure middle-object balance arrow, with identity native grades. -/
def balance (P : K) (Q : L) {Z Z' : C} (x : e.obj P ⟶ Z)
    (u : Z ⟶ Z') (y : Z' ⟶ d.obj Q) :
    (⟨Z, P, Q, x, u ≫ y⟩ : Object e d) ⟶ ⟨Z', P, Q, x ≫ u, y⟩ :=
  ⟨𝟙 _, u, 𝟙 _, by simp, by simp⟩

theorem balance_in_class (P : K) (Q : L) {Z Z' : C} (x : e.obj P ⟶ Z)
    (u : Z ⟶ Z') (y : Z' ⟶ d.obj Q) : balanceClass e d (balance e d P Q x u y) := by
  constructor <;> change IsIso (𝟙 _) <;> infer_instance

theorem balance_inverted (P : K) (Q : L) {Z Z' : C} (x : e.obj P ⟶ Z)
    (u : Z ⟶ Z') (y : Z' ⟶ d.obj Q) :
    IsIso ((balanceClass e d).Q.map (balance e d P Q x u y)) :=
  Localization.inverts (balanceClass e d).Q (balanceClass e d) _ (balance_in_class e d P Q x u y)

/-- In particular, a noninvertible native grade arrow is not made invertible. -/
theorem noninvertible_grade_retained {s t : Object e d} (f : s ⟶ t)
    (h : ¬ IsIso f.left ∨ ¬ IsIso f.right) : ¬ IsIso ((balanceClass e d).Q.map f) := by
  intro hi
  have hf := (localized_iso_iff e d f).mp hi
  rcases h with h | h
  · exact h hf.1
  · exact h hf.2

/-- Full native comma morphisms, not just objects, survive the inverse
normal-form comparison. -/
noncomputable def sectionFullyFaithful : (localizedSection e d).FullyFaithful :=
  (localizationEquivalence e d).fullyFaithfulInverse

theorem native_map_injective {s t : Comma e d} (f g : s ⟶ t)
    (h : (localizedSection e d).map f = (localizedSection e d).map g) : f = g :=
  (sectionFullyFaithful e d).faithful.map_injective h

noncomputable def universalProperty (D : Type*) [Category D] :
    (Comma e d ⥤ D) ≌ (balanceClass e d).FunctorsInverting D :=
  Localization.functorEquivalence (normalize e d) (balanceClass e d) D

/-- Inverting the derived normal-form contractions already suffices to
invert the whole declared balance class. No inverse of a native noniso is required. -/
theorem inverts_of_contractions {D : Type*} [Category D] (F : Object e d ⥤ D)
    (h : ∀ s, IsIso (F.map ((contraction e d).app s))) :
    (balanceClass e d).IsInvertedBy F := by
  intro s t f hf
  let := h s
  let := h t
  have hn : IsIso ((normalize e d).map f) := normalize_inverts e d f hf
  let := hn
  have hs : IsIso ((sectionFunctor e d).map ((normalize e d).map f)) :=
    (sectionFunctor e d).map_isIso _
  let := hs
  have he : F.map f = inv (F.map ((contraction e d).app s)) ≫
      F.map ((sectionFunctor e d).map ((normalize e d).map f)) ≫
        F.map ((contraction e d).app t) := by
    apply (cancel_epi (F.map ((contraction e d).app s))).mp
    simp only [IsIso.hom_inv_id_assoc]
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map ((contraction e d).naturality f).symm
  rw [he]
  infer_instance

end ContextualComposition.Factorization
