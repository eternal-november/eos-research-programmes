module

public import ContextualComposition.FinitePresentationCell

/-! Fixed-endpoint presentation classification and the local adjunction in (8). -/

@[expose] public section

namespace ContextualComposition.FiniteRelationPresentation

open FiniteNormalization (Presentation Difunctional)
open FiniteNormalization.Presentation (Cell)

universe u
variable {A B Y Z : Type u}

abbrev Unused (R : A → B → Prop) := {b // ¬ ∃ a, R a b}

/-- Target-block equality assembled from the nonempty rows and a partition on unused targets. -/
def sameBlock (R : A → B → Prop) (U : Setoid (Unused R)) (b c : B) : Prop :=
  (∃ a, R a b ∧ R a c) ∨ ∃ hb hc, U.r ⟨b, hb⟩ ⟨c, hc⟩

def blockSetoid (R : A → B → Prop) (hR : Difunctional R) (U : Setoid (Unused R)) : Setoid B where
  r := sameBlock R U
  iseqv := {
    refl := by
      intro b
      by_cases h : ∃ a, R a b
      · obtain ⟨a, ha⟩ := h
        exact Or.inl ⟨a, ha, ha⟩
      · exact Or.inr ⟨h, h, U.refl _⟩
    symm := by
      rintro b c (⟨a, hb, hc⟩ | ⟨hb, hc, h⟩)
      · exact Or.inl ⟨a, hc, hb⟩
      · exact Or.inr ⟨hc, hb, U.symm h⟩
    trans := by
      rintro b c d (⟨a, hb, hc⟩ | ⟨hb, hc, h⟩) (⟨a', hc', hd⟩ | ⟨hc', hd, h'⟩)
      · exact Or.inl ⟨a, hb, hR hc hc' hd⟩
      · exact False.elim (hc' ⟨a, hc⟩)
      · exact False.elim (hc ⟨a', hc'⟩)
      · exact Or.inr ⟨hb, hd, U.trans h h'⟩ }

noncomputable def build (R : A → B → Prop) (hR : Difunctional R) (U : Setoid (Unused R)) :
    Presentation A B (Quotient (blockSetoid R hR U)) where
  domain a := ∃ b, R a b
  block := Quotient.mk _
  onto := Quotient.exists_rep
  selected a := Quotient.mk _ a.property.choose

theorem build_row (R : A → B → Prop) (hR : Difunctional R) (U : Setoid (Unused R)) (a : A) (b : B) :
    (build R hR U).row a b ↔ R a b := by
  constructor
  · rintro ⟨h, eq⟩
    have conn : sameBlock R U h.choose b := Quotient.exact eq
    rcases conn with ⟨a', h₁, h₂⟩ | ⟨hn, _, _⟩
    · exact hR h.choose_spec h₁ h₂
    · exact False.elim (hn ⟨a, h.choose_spec⟩)
  · intro h
    let d : ∃ b', R a b' := ⟨b, h⟩
    exact ⟨d, Quotient.sound (show sameBlock R U d.choose b from Or.inl ⟨a, d.choose_spec, h⟩)⟩

theorem build_unused (R : A → B → Prop) (hR : Difunctional R) (U : Setoid (Unused R)) (b c : Unused R) :
    (build R hR U).block b.val = (build R hR U).block c.val ↔ U.r b c := by
  constructor
  · intro h
    have hd : sameBlock R U b.val c.val := Quotient.exact h
    rcases hd with ⟨a, hb, _⟩ | ⟨_, _, hr⟩
    · exact False.elim (b.property ⟨a, hb⟩)
    · exact hr
  · intro h
    exact Quotient.sound (show sameBlock R U b.val c.val from Or.inr ⟨b.property, c.property, h⟩)

/-- The unused-block partition read back from a named-quotient presentation. -/
def unusedPartition (P : Presentation A B Y) : Setoid (Unused P.row) where
  r b c := P.block b.val = P.block c.val
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- Recovering the relation and unused partition recovers the original block identifications on all targets. -/
theorem recover_blocks (P : Presentation A B Y) (b c : B) :
    sameBlock P.row (unusedPartition P) b c ↔ P.block b = P.block c := by
  constructor
  · rintro (⟨a, ⟨_, h₁⟩, _, h₂⟩ | ⟨_, _, h⟩)
    · exact h₁.symm.trans h₂
    · exact h
  · intro h
    by_cases hb : ∃ a, P.row a b
    · obtain ⟨a, ha, he⟩ := hb
      exact Or.inl ⟨a, ⟨ha, he⟩, ha, he.trans h⟩
    · have hc : ¬ ∃ a, P.row a c := by
        rintro ⟨a, ha, he⟩
        exact hb ⟨a, ha, he.trans h.symm⟩
      exact Or.inr ⟨hb, hc, h⟩

/-- In each direction the original and reconstructed labelled presentations have the unique native cell. -/
theorem recover_cells (P : Presentation A B Y) :
    let L := build P.row P.row_difunctional (unusedPartition P)
    Nonempty (Cell L P id id) ∧ Nonempty (Cell P L id id) := by
  constructor
  · apply FiniteNormalization.Presentation.cell_iff_row_blocks.mpr
    exact ⟨fun a b => (build_row _ _ _ a b).mp, fun b c e => (recover_blocks _ b c).mp (Quotient.exact e)⟩
  · apply FiniteNormalization.Presentation.cell_iff_row_blocks.mpr
    exact ⟨fun a b => (build_row _ _ _ a b).mpr, fun b c e => Quotient.sound ((recover_blocks _ b c).mpr e)⟩

/-- Mutual fixed-endpoint squares give inverse quotient-label maps. -/
theorem inverse_label_maps {P : Presentation A B Y} {Q : Presentation A B Z}
    (f : Cell P Q id id) (g : Cell Q P id id) :
    (∀ y, g.labelMap (f.labelMap y) = y) ∧ (∀ z, f.labelMap (g.labelMap z) = z) := by
  constructor
  · intro y
    obtain ⟨b, rfl⟩ := P.onto y
    exact (congrArg g.labelMap (f.block_comm b)).trans (g.block_comm b)
  · intro z
    obtain ⟨b, rfl⟩ := Q.onto z
    exact (congrArg f.labelMap (g.block_comm b)).trans (f.block_comm b)

/-- The order in the fibre over a fixed difunctional relation is exactly unused-block refinement. -/
theorem fibre_cell_iff (R : A → B → Prop) (hR : Difunctional R) (U V : Setoid (Unused R)) :
    Nonempty (Cell (build R hR U) (build R hR V) id id) ↔ ∀ b c, U.r b c → V.r b c := by
  constructor
  · intro h b c e
    apply (build_unused _ _ _ _ _).mp
    exact (FiniteNormalization.Presentation.cell_iff_row_blocks.mp h).2 _ _ ((build_unused _ _ _ _ _).mpr e)
  · intro h
    apply FiniteNormalization.Presentation.cell_iff_row_blocks.mpr
    constructor
    · exact fun a b e => (build_row _ _ _ a b).mpr ((build_row _ _ _ a b).mp e)
    · intro b c e
      apply Quotient.sound
      have hb : sameBlock R U b c := Quotient.exact e
      rcases hb with hrow | ⟨hb, hc, hbc⟩
      · exact Or.inl hrow
      · exact Or.inr ⟨hb, hc, h _ _ hbc⟩

/-- The discrete partition of unused targets defines the left adjoint F. -/
def discretePartition (R : A → B → Prop) : Setoid (Unused R) where
  r := Eq
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

noncomputable abbrev free (R : A → B → Prop) (hR : Difunctional R) :=
  build R hR (discretePartition R)

theorem row_free (R : A → B → Prop) (hR : Difunctional R) : (free R hR).row = R :=
  funext fun a => funext fun b => propext (build_row _ _ _ a b)

/-- The hom-preorder adjunction F ⊣ E for fixed endpoints; its left inverse equation is row_free. -/
theorem free_cell_iff (R : A → B → Prop) (hR : Difunctional R) (P : Presentation A B Y) :
    Nonempty (Cell (free R hR) P id id) ↔ ∀ a b, R a b → P.row a b := by
  constructor
  · rintro ⟨cell⟩ a b h
    exact cell.map_row ((build_row _ _ _ a b).mpr h)
  · intro h
    apply FiniteNormalization.Presentation.cell_iff_row_blocks.mpr
    constructor
    · exact fun a b hr => h a b ((build_row _ _ _ a b).mp hr)
    · intro b c e
      have hc : sameBlock R (discretePartition R) b c := Quotient.exact e
      rcases hc with ⟨a, hb, hc⟩ | ⟨_, _, hbc⟩
      · obtain ⟨_, eb⟩ := h a b hb
        obtain ⟨_, ec⟩ := h a c hc
        exact eb.symm.trans ec
      · exact congrArg (fun x : Unused R => P.block x.val) hbc

end ContextualComposition.FiniteRelationPresentation
