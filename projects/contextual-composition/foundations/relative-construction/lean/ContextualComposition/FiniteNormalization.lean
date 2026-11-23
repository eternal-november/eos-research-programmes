module

public import ContextualComposition.FiniteDescent
import all ContextualComposition.FiniteDescent

/-! Partial-domain normalization, equations (5) and (6) of the mixed normal-form reduction report. The argument applies in particular to finite sets and requires no enumeration of either endpoint. -/

@[expose] public section

namespace ContextualComposition.FiniteNormalization

open ContextualComposition.FiniteDescent (Pushout left right glue_eq descend)

universe u
variable {A B C E Y Z : Type u}

/-- A subdomain, a surjection naming the target blocks, and a selected block on each defined input. -/
structure Presentation (A B Y : Type u) where
  domain : A → Prop
  block : B → Y
  onto : ∀ y, ∃ b, block b = y
  selected : {a // domain a} → Y

def Presentation.row (P : Presentation A B Y) (a : A) (b : B) : Prop :=
  ∃ h : P.domain a, P.selected ⟨a, h⟩ = P.block b

/-- Labels touched by the second domain, with the restricted first quotient as a surjection onto its image. -/
def Active (q : E → Y) (y : Y) : Prop := ∃ e, q e = y

def activeMap (q : E → Y) (e : E) : {y // Active q y} := ⟨q e, e, rfl⟩

variable (q : E → Y) (g : E → Z) (r : C → Z)

/-- The quotient-output map in (5) is onto, including when the second domain is empty. -/
theorem output_onto (hr : ∀ z, ∃ c, r c = z) (x : Pushout (activeMap q) g) :
    ∃ c, right (activeMap q) g (r c) = x := by
  induction x using Quot.ind with
  | _ x =>
    cases x with
    | inr z =>
      obtain ⟨c, rfl⟩ := hr z
      exact ⟨c, rfl⟩
    | inl w =>
      obtain ⟨y, e, rfl⟩ := w
      obtain ⟨c, hc⟩ := hr (g e)
      exact ⟨c, (congrArg (right (activeMap q) g) hc).trans (glue_eq e).symm⟩

def Presentation.middle (P : Presentation A B Y) (Q : Presentation B C Z) (e : {b // Q.domain b}) : Y := P.block e.val

/-- Formula (5), using the pullback of the active labels as source domain. -/
noncomputable def Presentation.comp (P : Presentation A B Y) (Q : Presentation B C Z) :
    Presentation A C (Pushout (activeMap (P.middle Q)) Q.selected) where
  domain a := ∃ h : P.domain a, Active (P.middle Q) (P.selected ⟨a, h⟩)
  selected a := left _ _ ⟨P.selected ⟨a.val, a.property.choose⟩, a.property.choose_spec⟩
  block c := right _ _ (Q.block c)
  onto := output_onto _ _ _ Q.onto

def Difunctional (R : Y → C → Prop) : Prop :=
  ∀ ⦃y y' c c'⦄, R y c → R y' c → R y' c' → R y c'

/-- Intersection of the difunctional upper bounds. -/
def closure (M : Y → C → Prop) (y : Y) (c : C) : Prop :=
  ∀ R : Y → C → Prop, Difunctional R → (∀ y' c', M y' c' → R y' c') → R y c

theorem closure_difunctional (M : Y → C → Prop) : Difunctional (closure M) :=
  fun _ _ _ _ h₁ h₂ h₃ R hR hM => hR (h₁ R hR hM) (h₂ R hR hM) (h₃ R hR hM)

theorem closure_extensive (M : Y → C → Prop) {y c} (h : M y c) : closure M y c :=
  fun _ _ hM => hM y c h

/-- The expanded incidence relation before restricting back to selected labels. -/
def expanded (y : Y) (c : C) : Prop := ∃ e, q e = y ∧ g e = r c

def connected (y : Y) (c : C) : Prop :=
  ∃ h : Active q y, left (activeMap q) g ⟨y, h⟩ = right (activeMap q) g (r c)

theorem connected_difunctional : Difunctional (connected q g r) := by
  intro y y' c c' h₁ h₂ h₃
  obtain ⟨h, e₁⟩ := h₁
  obtain ⟨_, e₂⟩ := h₂
  obtain ⟨_, e₃⟩ := h₃
  exact ⟨h, e₁.trans (e₂.symm.trans e₃)⟩

theorem expanded_connected (y c) : expanded q g r y c → connected q g r y c := by
  rintro ⟨e, rfl, he⟩
  exact ⟨⟨e, rfl⟩, (glue_eq e).trans (congrArg (right (activeMap q) g) he)⟩

/-- Pushout connectivity is exactly the least difunctional upper bound of expanded incidence. -/
theorem connected_iff_closure (hr : ∀ z, ∃ c, r c = z) (y : Y) (c : C) :
    connected q g r y c ↔ closure (expanded q g r) y c := by
  constructor
  · rintro ⟨hy, path⟩ R hR hM
    -- Extend the column of R at c to a predicate on the pushout by descent.
    let l (w : {y // Active q y}) : Prop := R w.val c
    let s (z : Z) : Prop := ∀ e, g e = z → R (q e) c
    have compat (e : E) : l (activeMap q e) = s (g e) := by
      apply propext
      constructor
      · intro h e' he'
        obtain ⟨b, hb⟩ := hr (g e)
        exact hR (hM _ _ ⟨e', rfl, he'.trans hb.symm⟩) (hM _ _ ⟨e, rfl, hb.symm⟩) h
      · intro h
        exact h e rfl
    have eq := congrArg (descend l s compat) path
    have rhs : s (r c) := fun e he => hM _ _ ⟨e, rfl, he⟩
    exact Eq.mpr eq rhs
  · intro h
    exact h _ (connected_difunctional q g r) (expanded_connected q g r)

/-- Formula (6) with all source-domain and active-label conditions retained. -/
theorem row_comp_iff (P : Presentation A B Y) (Q : Presentation B C Z) (a : A) (c : C) :
    (P.comp Q).row a c ↔ ∃ h : P.domain a, closure (expanded (P.middle Q) Q.selected Q.block) (P.selected ⟨a, h⟩) c := by
  constructor
  · rintro ⟨⟨h, ha⟩, e⟩
    exact ⟨h, (connected_iff_closure _ _ _ Q.onto _ _).mp ⟨ha, e⟩⟩
  · rintro ⟨h, hc⟩
    obtain ⟨ha, e⟩ := (connected_iff_closure _ _ _ Q.onto _ _).mpr hc
    exact ⟨⟨h, ha⟩, e⟩

theorem Presentation.row_difunctional (P : Presentation A B Y) : Difunctional P.row := by
  rintro a a' b b' ⟨ha, e₁⟩ ⟨_, e₂⟩ ⟨_, e₃⟩
  exact ⟨ha, e₁.trans (e₂.symm.trans e₃)⟩

def ordinary (P : Presentation A B Y) (Q : Presentation B C Z) (a : A) (c : C) : Prop :=
  ∃ b, P.row a b ∧ Q.row b c

theorem ordinary_iff_expanded (P : Presentation A B Y) (Q : Presentation B C Z) (a : A) (c : C) :
    ordinary P Q a c ↔ ∃ ha : P.domain a, expanded (P.middle Q) Q.selected Q.block (P.selected ⟨a, ha⟩) c := by
  constructor
  · rintro ⟨b, ⟨ha, ea⟩, hb, eb⟩
    exact ⟨ha, ⟨b, hb⟩, ea.symm, eb⟩
  · rintro ⟨ha, e, ea, ec⟩
    exact ⟨e.val, ⟨ha, ea.symm⟩, e.property, ec⟩

theorem ordinary_closure_le (P : Presentation A B Y) (Q : Presentation B C Z) (a : A) (c : C) :
    closure (ordinary P Q) a c → (P.comp Q).row a c := by
  intro h
  apply h _ (P.comp Q).row_difunctional
  intro a' c' h'
  obtain ⟨ha, he⟩ := (ordinary_iff_expanded P Q a' c').mp h'
  exact (row_comp_iff P Q a' c').mpr ⟨ha, closure_extensive _ he⟩

/-- Every first quotient label touched by the second domain is selected by a first input. -/
def ActiveTight (P : Presentation A B Y) (Q : Presentation B C Z) : Prop :=
  ∀ y, Active (P.middle Q) y → ∃ a : {a // P.domain a}, P.selected a = y

/-- Formula (7). Active-tightness is a sufficient hypothesis for exchanging selection and closure. -/
theorem row_comp_iff_ordinary_closure (P : Presentation A B Y) (Q : Presentation B C Z)
    (ht : ActiveTight P Q) (a : A) (c : C) :
    (P.comp Q).row a c ↔ closure (ordinary P Q) a c := by
  refine ⟨?_, ordinary_closure_le P Q a c⟩
  intro h R hR hT
  obtain ⟨ha, hM⟩ := (row_comp_iff P Q a c).mp h
  -- Lift a difunctional upper bound back to the selected labels. Each lifted row uses all its selectors.
  let S (y : Y) (c' : C) : Prop :=
    (∃ d : {a // P.domain a}, P.selected d = y) ∧
    ∀ d : {a // P.domain a}, P.selected d = y → R d.val c'
  have hS : Difunctional S := by
    rintro y y' c₁ c₂ ⟨sel, h₁⟩ ⟨⟨d', hd'⟩, h₂⟩ ⟨_, h₃⟩
    exact ⟨sel, fun d hd => hR (h₁ d hd) (h₂ d' hd') (h₃ d' hd')⟩
  have hExt (y c') (m : expanded (P.middle Q) Q.selected Q.block y c') : S y c' := by
    obtain ⟨e, ey, ec⟩ := m
    refine ⟨ht y ⟨e, ey⟩, ?_⟩
    intro d hd
    exact hT _ _ ⟨e.val, ⟨d.property, hd.trans ey.symm⟩, e.property, ec⟩
  exact (hM S hS hExt).2 ⟨a, ha⟩ rfl

end ContextualComposition.FiniteNormalization
