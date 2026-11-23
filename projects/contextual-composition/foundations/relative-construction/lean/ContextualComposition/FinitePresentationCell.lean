module

public import ContextualComposition.FiniteNormalization

/-! Native squares for the finite mono/surjection presentations, including arbitrary endpoint maps. -/

@[expose] public section

namespace ContextualComposition.FiniteNormalization.Presentation

universe u
variable {A B A' B' Y Z : Type u}

/-- Both grade maps of a square. The map on the subdomain is forced over its endpoint map. -/
structure Cell (P : Presentation A B Y) (Q : Presentation A' B' Z) (s : A → A') (t : B → B') where
  domainMap : ∀ a, P.domain a → Q.domain (s a)
  labelMap : Y → Z
  block_comm : ∀ b, labelMap (P.block b) = Q.block (t b)
  selected_comm : ∀ d, labelMap (P.selected d) = Q.selected ⟨s d.val, domainMap d.val d.property⟩

variable {P : Presentation A B Y} {Q : Presentation A' B' Z} {s : A → A'} {t : B → B'}

instance : Subsingleton (Cell P Q s t) where
  allEq x y := by
    have h : x.labelMap = y.labelMap := by
      funext i
      obtain ⟨b, rfl⟩ := P.onto i
      exact (x.block_comm b).trans (y.block_comm b).symm
    cases x
    cases y
    cases h
    rfl

theorem Cell.map_row (cell : Cell P Q s t) {a b} (h : P.row a b) : Q.row (s a) (t b) := by
  obtain ⟨ha, e⟩ := h
  exact ⟨cell.domainMap a ha, (cell.selected_comm ⟨a, ha⟩).symm.trans ((congrArg cell.labelMap e).trans (cell.block_comm b))⟩

/-- Preservation of rows and of target-block identifications constructs the unique square. -/
noncomputable def Cell.ofRowBlocks (hrow : ∀ a b, P.row a b → Q.row (s a) (t b))
    (hblock : ∀ b b', P.block b = P.block b' → Q.block (t b) = Q.block (t b')) : Cell P Q s t := by
  let f (y : Y) := Q.block (t (P.onto y).choose)
  have hf (b : B) : f (P.block b) = Q.block (t b) :=
    hblock _ _ (P.onto (P.block b)).choose_spec
  have hd (a : A) (h : P.domain a) : Q.domain (s a) := by
    obtain ⟨b, eb⟩ := P.onto (P.selected ⟨a, h⟩)
    exact (hrow a b ⟨h, eb.symm⟩).choose
  refine ⟨hd, f, hf, ?_⟩
  intro d
  obtain ⟨b, eb⟩ := P.onto (P.selected d)
  obtain ⟨_, hb⟩ := hrow d.val b ⟨d.property, eb.symm⟩
  exact ((congrArg f eb.symm).trans (hf b)).trans hb.symm

theorem cell_iff_row_blocks :
    Nonempty (Cell P Q s t) ↔
    (∀ a b, P.row a b → Q.row (s a) (t b)) ∧
    (∀ b b', P.block b = P.block b' → Q.block (t b) = Q.block (t b')) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨fun _ _ => f.map_row, fun b b' e => (f.block_comm b).symm.trans ((congrArg f.labelMap e).trans (f.block_comm b'))⟩
  · rintro ⟨hr, hb⟩
    exact ⟨Cell.ofRowBlocks hr hb⟩

end ContextualComposition.FiniteNormalization.Presentation
