module

public import ContextualComposition.CorelationSplitting
public import ContextualComposition.FinitePresentationCell

/-! The corelation of a partial normal form and its native squares, §3 of
the presentation-cell reduction. Endpoints may change along arbitrary functions.
-/

@[expose] public section

namespace ContextualComposition.PresentationCorelation

open FiniteNormalization (Presentation)
open CorelationSplitting (MeetsTarget Normal Refines)

universe u
variable {A B Y A' B' Z : Type u}

/-- The two tags distinguish an undefined source singleton from a quotient label. -/
noncomputable def key (P : Presentation A B Y) : Sum A B → Sum A Y := by
  classical
  exact Sum.elim (fun a => if h : P.domain a then .inr (P.selected ⟨a,h⟩) else .inl a)
    (fun b => .inr (P.block b))

def embed (P : Presentation A B Y) : Setoid (Sum A B) where
  r x y := key P x = key P y
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem source_target (P : Presentation A B Y) (a : A) (b : B) :
    (embed P).r (.inl a) (.inr b) ↔ P.row a b := by
  classical
  change key P (.inl a) = key P (.inr b) ↔ _
  by_cases h : P.domain a
  · simp [key, Presentation.row, h, Sum.elim]
  · constructor
    · simp [key, h, Sum.elim]
    · rintro ⟨ha, _⟩; exact False.elim (h ha)

theorem target_target (P : Presentation A B Y) (b b' : B) :
    (embed P).r (.inr b) (.inr b') ↔ P.block b = P.block b' :=
  ⟨Sum.inr.inj, congrArg Sum.inr⟩

theorem domain_iff_meets (P : Presentation A B Y) (a : A) :
    P.domain a ↔ MeetsTarget (embed P) (.inl a) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := P.onto (P.selected ⟨a,h⟩)
    exact ⟨b, (source_target _ _ _).mpr ⟨h, hb.symm⟩⟩
  · rintro ⟨b,h⟩
    exact ((source_target _ _ _).mp h).choose

theorem embed_normal (P : Presentation A B Y) : Normal (embed P) := by
  classical
  intro x y h
  cases x with
  | inr b => exact Or.inr ⟨b, rfl⟩
  | inl a =>
    by_cases ha : P.domain a
    · exact Or.inr ((domain_iff_meets _ _).mp ha)
    · left
      cases y with
      | inr b => exact False.elim (ha (((source_target _ _ _).mp h).choose))
      | inl a' =>
        change key P (.inl a) = key P (.inl a') at h
        by_cases ha' : P.domain a' <;> simp_all [key, Sum.elim]

def Square (P : Setoid (Sum A B)) (Q : Setoid (Sum A' B')) (s : A → A') (t : B → B') : Prop :=
  ∀ x y, P.r x y → Q.r (Sum.map s t x) (Sum.map s t y)

/-- The native cell pushes forward every block, even if some previously
undefined source points gain a label. -/
theorem square_of_cell (P : Presentation A B Y) (Q : Presentation A' B' Z)
    (s : A → A') (t : B → B') (f : P.Cell Q s t) : Square (embed P) (embed Q) s t := by
  classical
  let lift : Sum A Y → Sum A' Z := Sum.elim (fun a => key Q (.inl (s a))) (fun y => .inr (f.labelMap y))
  have commute (x : Sum A B) : lift (key P x) = key Q (Sum.map s t x) := by
    cases x with
    | inr b => exact congrArg Sum.inr (f.block_comm b)
    | inl a =>
      by_cases ha : P.domain a
      · have hb := f.domainMap a ha
        simpa [lift, key, Sum.elim, ha, hb] using congrArg (Sum.inr (α := A')) (f.selected_comm ⟨a,ha⟩)
      · simp [lift, key, Sum.elim, ha]
  intro x y h
  exact (commute x).symm.trans ((congrArg lift h).trans (commute y))

/-- Recover the forward label map by choosing a preimage of each source
label. Preservation of target-target equivalence makes this map independent
of the chosen preimage. -/
noncomputable def cell_of_square (P : Presentation A B Y) (Q : Presentation A' B' Z)
    (s : A → A') (t : B → B') (h : Square (embed P) (embed Q) s t) : P.Cell Q s t := by
  apply Presentation.Cell.ofRowBlocks
  · intro a b hab
    exact (source_target _ _ _).mp (h _ _ ((source_target _ _ _).mpr hab))
  · intro b b' hbb
    exact (target_target Q _ _).mp (h _ _ ((target_target P _ _).mpr hbb))

/-- Individual squares correspond over every pair of endpoint maps.
The native cell is unique by surjectivity of the first block map. -/
theorem native_square_iff (P : Presentation A B Y) (Q : Presentation A' B' Z)
    (s : A → A') (t : B → B') :
    Nonempty (P.Cell Q s t) ↔ Square (embed P) (embed Q) s t :=
  ⟨fun ⟨f⟩ => square_of_cell P Q s t f, fun h => ⟨cell_of_square P Q s t h⟩⟩

/-- Target labels recovered from a partition are its blocks on the target subset. -/
def targetSetoid (S : Setoid (Sum A B)) : Setoid B where
  r b c := S.r (.inr b) (.inr c)
  iseqv := ⟨fun _ => S.refl _, fun h => S.symm h, fun h k => S.trans h k⟩

noncomputable def recover (S : Setoid (Sum A B)) : Presentation A B (Quotient (targetSetoid S)) where
  domain a := MeetsTarget S (.inl a)
  block := Quotient.mk _
  onto y := Quotient.inductionOn y (fun b => ⟨b,rfl⟩)
  selected a := Quotient.mk _ a.property.choose

theorem recover_test (S : Setoid (Sum A B)) (x : Sum A B) (b : B) :
    (embed (recover S)).r x (.inr b) ↔ S.r x (.inr b) := by
  cases x with
  | inr c =>
    exact (target_target _ _ _).trans ⟨Quotient.exact, fun h => Quotient.sound (s := targetSetoid S) h⟩
  | inl a =>
    rw [source_target]
    constructor
    · rintro ⟨ha, eq⟩
      exact S.trans ha.choose_spec (Quotient.exact eq : (targetSetoid S).r ha.choose b)
    · intro h
      have hd : MeetsTarget S (.inl a) := ⟨b,h⟩
      exact ⟨hd, Quotient.sound (S.trans (S.symm hd.choose_spec) h : (targetSetoid S).r hd.choose b)⟩

private theorem transfer_normal {S T : Setoid (Sum A B)} (hS : Normal S)
    (h : ∀ x b, S.r x (.inr b) ↔ T.r x (.inr b)) : Refines S T := by
  intro x y xy
  rcases hS _ _ xy with rfl | ⟨b, xb⟩
  · exact T.refl _
  · exact T.trans ((h x b).mp xb) (T.symm ((h y b).mp (S.trans (S.symm xy) xb)))

/-- Every normalized partition is the literal embedded partition of its recovered
presentation. This identifies the normalized image used in the local coreflection. -/
theorem embed_recover (S : Setoid (Sum A B)) (hS : Normal S) : embed (recover S) = S := by
  have h₁ := transfer_normal (embed_normal (recover S)) (recover_test S)
  have h₂ := transfer_normal hS (fun x b => (recover_test S x b).symm)
  have eqr : (embed (recover S)).r = S.r := funext fun x => funext fun y => propext ⟨h₁ x y, h₂ x y⟩
  exact (show ∀ P Q : Setoid (Sum A B), P.r = Q.r → P = Q by
    intro ⟨_, _⟩ ⟨_, _⟩ h; cases h; rfl) _ _ eqr

end ContextualComposition.PresentationCorelation
