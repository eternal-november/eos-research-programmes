module

public import ContextualComposition.PresentationCorelation
import all ContextualComposition.FiniteDescent

/-! Equation (10) of the mixed normal-form reduction report. The composite
of two presented corelations is the kernel partition on the outer endpoints
of the pushout cospan. Taking this kernel discards any component with no
outer endpoint. -/

@[expose] public section
namespace ContextualComposition.CorelationComposition

open FiniteDescent (Pushout left right glue_eq descend)
open FiniteNormalization (Presentation activeMap Active)
open CorelationSplitting (Normal Refines split)
open PresentationCorelation (key embed)

universe u
variable {A B C Y Z : Type u}

/-- Two cospans presented by endpoint maps to their sets of labels. -/
def outer {L R : Type u} (p : Sum A B → L) (q : Sum B C → R) :
    Sum A C → Pushout (fun b => p (.inr b)) (fun b => q (.inl b)) :=
  Sum.elim (fun a => left _ _ (p (.inl a))) (fun c => right _ _ (q (.inr c)))

/-- Kernel of the induced outer map to the pushout. Unused cospan apex
points contribute no class on the outer endpoints. -/
def compose {L R : Type u} (p : Sum A B → L) (q : Sum B C → R) : Setoid (Sum A C) where
  r x y := outer p q x = outer p q y
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

variable (P : Presentation A B Y) (Q : Presentation B C Z)

private abbrev Small := Pushout (activeMap (P.middle Q)) Q.selected
private abbrev Big := Pushout (fun b => key P (.inr b)) (fun b => key Q (.inl b))

/-- An active first label lands in the normalization pushout. Every inactive
first label is retained separately until source-only classes are split. -/
private noncomputable def firstLabel (y : Y) : Sum (Sum A Y) (Small P Q) := by
  classical
  exact if hy : Active (P.middle Q) y then .inr (left _ _ ⟨y,hy⟩) else .inl (.inr y)

private noncomputable def codeLeft : Sum A Y → Sum (Sum A Y) (Small P Q) :=
  Sum.elim (fun a => .inl (.inl a)) (firstLabel P Q)

private noncomputable def codeRight : Sum B Z → Sum (Sum A Y) (Small P Q) :=
  Sum.elim (fun b => firstLabel P Q (P.block b)) (fun z => .inr (right _ _ z))

private theorem code_comm (b : B) :
    codeLeft P Q (key P (.inr b)) = codeRight P Q (key Q (.inl b)) := by
  classical
  by_cases hb : Q.domain b
  · have hy : Active (P.middle Q) (P.block b) := ⟨⟨b,hb⟩,rfl⟩
    simpa [Small, key, codeLeft, codeRight, firstLabel, Sum.elim, hb, hy, activeMap, Presentation.middle] using
      congrArg (Sum.inr (α := Sum A Y)) (glue_eq (q := activeMap (P.middle Q)) (g := Q.selected) ⟨b,hb⟩)
  · simp [codeLeft, codeRight, key, hb, Sum.elim]

private noncomputable def code : Big P Q → Sum (Sum A Y) (Small P Q) :=
  descend (codeLeft P Q) (codeRight P Q) (code_comm P Q)

/-- Each generator of the active-label pushout is already a gluing in
the unpruned cospan pushout. -/
private noncomputable def smallToBig : Small P Q → Big P Q := by
  refine descend (fun w => left _ _ (.inr w.val)) (fun z => right _ _ (.inr z)) ?_
  intro e
  simpa [Big, key, Sum.elim, e.property, activeMap, Presentation.middle] using
    (glue_eq (q := fun b => key P (.inr b)) (g := fun b => key Q (.inl b)) e.val)

/-- The source-to-target incidence test is identical before and after
normalization. A source label which loses all targets has no such incidence. -/
theorem source_test (a : A) (c : C) :
    (embed (P.comp Q)).r (.inl a) (.inr c) ↔ (compose (key P) (key Q)).r (.inl a) (.inr c) := by
  classical
  rw [PresentationCorelation.source_target]
  constructor
  · rintro ⟨hd, he⟩
    obtain ⟨ha, hy⟩ := hd
    change left _ _ (key P (.inl a)) = right _ _ (key Q (.inr c))
    simpa [Big, key, ha, Sum.elim, Presentation.comp, smallToBig, descend, left, right] using congrArg (smallToBig P Q) he
  · intro he
    change left _ _ (key P (.inl a)) = right _ _ (key Q (.inr c)) at he
    have eq := congrArg (code P Q) he
    change codeLeft P Q (key P (.inl a)) = codeRight P Q (key Q (.inr c)) at eq
    by_cases ha : P.domain a
    · by_cases hy : Active (P.middle Q) (P.selected ⟨a,ha⟩)
      · refine ⟨⟨ha,hy⟩, ?_⟩
        simpa [Small, Presentation.comp, key, codeLeft, codeRight, firstLabel, Sum.elim, ha, hy] using eq
      · simp [key, codeLeft, codeRight, firstLabel, Sum.elim, ha, hy] at eq
    · simp [key, codeLeft, codeRight, Sum.elim, ha] at eq

theorem target_test (c d : C) :
    (embed (P.comp Q)).r (.inr c) (.inr d) ↔ (compose (key P) (key Q)).r (.inr c) (.inr d) := by
  rw [PresentationCorelation.target_target]
  constructor
  · intro h
    exact congrArg (smallToBig P Q) h
  · intro h
    exact Sum.inr.inj (congrArg (code P Q) h)

private theorem split_test (S : Setoid (Sum A C)) (x : Sum A C) (c : C) :
    (split S).r x (.inr c) ↔ S.r x (.inr c) :=
  ⟨CorelationSplitting.split_refines S _ _, fun h => Or.inr ⟨h,c,h⟩⟩

private theorem normal_ext {S T : Setoid (Sum A C)} (nT : Normal T) (nS : Normal S)
    (tests : ∀ x c, T.r x (.inr c) ↔ S.r x (.inr c)) : T = S := by
  have recoverRow {U V : Setoid (Sum A C)} (hn : Normal U)
      (hh : ∀ x c, U.r x (.inr c) → V.r x (.inr c)) : Refines U V := by
    intro x y e
    rcases hn _ _ e with rfl | ⟨c, hc⟩
    · exact V.refl _
    · exact V.trans (hh _ _ hc) (V.symm (hh _ _ (U.trans (U.symm e) hc)))
  have h₁ : Refines T S := recoverRow nT (fun x c => (tests x c).mp)
  have h₂ : Refines S T := recoverRow nS (fun x c => (tests x c).mpr)
  have eqr : T.r = S.r := funext fun x => funext fun y => propext ⟨h₁ x y, h₂ x y⟩
  exact (show ∀ P Q : Setoid (Sum A C), P.r = Q.r → P = Q by
    intro ⟨_, _⟩ ⟨_, _⟩ h; cases h; rfl) _ _ eqr

/-- After splitting source-only classes, the actual cospan pushout yields
exactly the partition of the normalized composite, including unused outputs. -/
theorem normalized_composition :
    embed (P.comp Q) = split (compose (key P) (key Q)) := by
  apply normal_ext (PresentationCorelation.embed_normal _) (CorelationSplitting.split_normal _)
  intro x c
  apply Iff.trans _ (split_test _ _ _).symm
  cases x with
  | inl a => exact source_test P Q a c
  | inr d => exact target_test P Q d c

theorem embed_recover_split (S : Setoid (Sum A B)) :
    embed (PresentationCorelation.recover S) = split S :=
  normal_ext (PresentationCorelation.embed_normal _) (CorelationSplitting.split_normal _)
    (fun x b => (PresentationCorelation.recover_test S x b).trans (split_test S x b).symm)

/-- Equation (9) expressed at the actual native cell interface. -/
theorem coreflection_cell (S : Setoid (Sum A B)) :
    Refines (embed P) S ↔ Nonempty (P.Cell (PresentationCorelation.recover S) id id) := by
  rw [PresentationCorelation.native_square_iff, CorelationSplitting.coreflection _ _ (PresentationCorelation.embed_normal P)]
  rw [← embed_recover_split S]
  constructor <;> intro h x y e <;> simpa using h x y e

/-- A total constant map followed by a nowhere-defined partial map. -/
def collapse : Presentation Bool Unit Unit where
  domain _ := True
  block := id
  onto c := ⟨c,rfl⟩
  selected _ := ()

def nowhere (X : Type) : Presentation X Unit Unit where
  domain _ := False
  block := id
  onto c := ⟨c,rfl⟩
  selected a := False.elim a.property

/-- The native partial composite has empty domain, including both source inputs. -/
theorem partial_composite_empty (a : Bool) :
    ¬ (collapse.comp (nowhere Unit)).domain a := by
  rintro ⟨_, ⟨_, hb⟩, _⟩
  exact hb

/-- Unpruned corelation composition preserves the connection between the
two inputs sent to the same middle point. Native partial composition makes
them separate undefined-source singletons. -/
theorem partial_map_nonconservative :
    compose (key collapse) (key (nowhere Unit)) ≠ embed (collapse.comp (nowhere Unit)) := by
  intro h
  have he : key collapse (.inl false) = key collapse (.inl true) := by simp [key, collapse, Sum.elim]
  have e : (compose (key collapse) (key (nowhere Unit))).r (.inl false) (.inl true) :=
    congrArg (left _ _) he
  rw [h] at e
  change key (collapse.comp (nowhere Unit)) (.inl false) = key (collapse.comp (nowhere Unit)) (.inl true) at e
  simp [key, partial_composite_empty, Sum.elim] at e

end ContextualComposition.CorelationComposition
