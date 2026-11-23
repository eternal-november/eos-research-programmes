module

public import ContextualComposition.DirectedStateBoundaries
public import ContextualComposition.DirectedStateSlideInterchange
public import Mathlib.CategoryTheory.Localization.Construction

/-! Selective inversion of state slides. The remaining state coordinate can still detect a noninvertible comparison after the other coordinate is localized. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.SelectiveStateContraction

open CategoryTheory DirectedStateBalance DirectedStateSlideInterchange DirectedStateBoundary
universe u v w d
variable {S : Type u} [Category.{v} S] (F : Diagram.{v,u,w,d} S) (P : MorphismProperty S)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

inductive Marked : {a b : Balance F} → (a ⟶ b) → Prop
  | slide {i j : S} (h : i ⟶ j) (isMarked : P h) (x : atPair F j i) : Marked ((DirectedStateBalance.slide F h).app x)

abbrev selected : MorphismProperty (Balance F) := @Marked _ _ F P
abbrev Localized := (selected F P).Localization
abbrev localization := (selected F P).Q

theorem inverts_iff {D : Type*} [Category* D] (K : Balance F ⥤ D) :
    (selected F P).IsInvertedBy K ↔ ∀ {i j} (h : i ⟶ j) (_ : P h) (x : atPair F j i), IsIso (K.map ((slide F h).app x)) := by
  constructor
  · exact fun a _ _ h hp x => a _ (.slide h hp x)
  · intro a i j m hm
    cases hm with | slide f hf z => exact a f hf z

theorem marked_iso {i j} (h : i ⟶ j) (hp : P h) (x : atPair F j i) :
    IsIso ((localization F P).map ((slide F h).app x)) := (selected F P).Q_inverts _ (.slide h hp x)

def extend {D : Type*} [Category* D] (c : DirectedStateBalance.Cocone F D)
    (ok : ∀ {i j} (h : i ⟶ j) (_ : P h) (x : atPair F j i), IsIso ((c.bal h).app x)) :
    Localized F P ⥤ D := Localization.Construction.lift c.descend ((inverts_iff F P _).mpr (fun h hp x => by
      have eq : c.descend.map ((slide F h).app x) = (c.bal h).app x := c.descend_generator (.slide h x)
      rw [eq]; exact ok h hp x))

theorem localized_data {D : Type*} [Category* D] (c : DirectedStateBalance.Cocone F D)
    (ok : ∀ {i j} (h : i ⟶ j) (_ : P h) (x : atPair F j i), IsIso ((c.bal h).app x)) :
    localization F P ⋙ extend F P c ok = c.descend := Localization.Construction.fac _ _

def universalProperty (D : Type*) [Category* D] :
    (Localized F P ⥤ D) ≌ (selected F P).FunctorsInverting D :=
  Localization.Construction.whiskeringLeftEquivalence _ _

variable {T : Type*} [Category* T]
inductive Vertical : {x y : S × T} → (x ⟶ y) → Prop where
  | mk (s : S) {t t' : T} (h : t ⟶ t') : Vertical (vertical s h)

abbrev verticalMarks (S : Type*) [Category* S] (T : Type*) [Category* T] :
    MorphismProperty (S × T) := @Vertical S _ T _

variable (G : Diagram (S × T))

def firstLabel : Balance G ⥤ S := state G ⋙ CategoryTheory.Prod.fst S T

theorem first_inverts : (selected G (verticalMarks S T)).IsInvertedBy (firstLabel G) := by
  apply (inverts_iff _ _ _).mpr
  intro i j h hh x
  cases hh with
  | mk s k =>
    have e : (firstLabel G).map ((slide G (vertical s k)).app x) = 𝟙 s := congrArg Prod.fst (slide_label G _ x)
    exact e.symm ▸ (inferInstance : IsIso (𝟙 s))

/-- Localization at every second-coordinate slide cannot turn a noninvertible first-coordinate state map into an invertible slide. -/
theorem horizontal_directed {s s' : S} (h : s ⟶ s') (t : T) (x : atPair G (s',t) (s,t)) (no : ¬IsIso h) :
    ¬IsIso ((localization G (verticalMarks S T)).map ((slide G (horizontal h t)).app x)) := by
  intro invert
  let P := selected G (verticalMarks S T)
  let K := Localization.Construction.lift (firstLabel G) (first_inverts G)
  let m := (slide G (horizontal h t)).app x
  have h₁ : IsIso ((P.Q ⋙ K).map m) := K.map_isIso (P.Q.map m)
  have e := Localization.Construction.fac (firstLabel G) (first_inverts G)
  have h₂ : IsIso ((firstLabel G).map m) := congrArg (fun k : Balance G ⥤ S => IsIso (k.map m)) e ▸ h₁
  have eq : (firstLabel G).map m = h := congrArg Prod.fst (slide_label G _ x)
  exact no (eq ▸ h₂)

end ContextualComposition.SelectiveStateContraction
