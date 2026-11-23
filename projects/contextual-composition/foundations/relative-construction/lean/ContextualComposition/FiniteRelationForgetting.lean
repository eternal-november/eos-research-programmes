module
public import ContextualComposition.FinitePresentationCell
import all ContextualComposition.FiniteDescent

/-! The unused-block example as actual native cells and as an obstruction to binary descent for the general partial-domain composition. -/

@[expose] public section
namespace ContextualComposition.FiniteRelationForgetting
open FiniteNormalization
open FiniteDescent (Middle coarsen continuation)

universe u
variable {A B Y : Type u}

def onTotal (P : FiniteDescent.Presentation A B Y) : Presentation A B Y where
  domain _ := True
  block := P.block
  onto := P.onto
  selected a := P.selected a.val

def pure (f : A → B) : Presentation A B B :=
  ⟨fun _ => True, id, fun b => ⟨b,rfl⟩, fun a => f a.val⟩

abbrev fine := onTotal FiniteDescent.fine
abbrev coarse := onTotal FiniteDescent.coarse

theorem same_observation : fine.row = coarse.row := by
  funext a b
  apply propext
  change (∃ _ : True, FiniteDescent.fine.row a b) ↔ ∃ _ : True, FiniteDescent.coarse.row a b
  rw [FiniteDescent.same_input]

def forwardCell : fine.Cell coarse id id where
  domainMap _ _ := trivial
  labelMap := coarsen
  block_comm b := FiniteDescent.coarsening_cell.1 b
  selected_comm d := FiniteDescent.coarsening_cell.2.1 d.val

/-- The coarsening becomes equality on relations, although it has no native inverse cell. -/
theorem no_reverse_cell : ¬ Nonempty (coarse.Cell fine id id) := by
  rintro ⟨g⟩
  have h : Middle.one = Middle.two := (g.block_comm Middle.one).symm.trans (g.block_comm Middle.two)
  cases h

theorem fine_after (a : Unit) (c : Bool) : (fine.comp (pure continuation)).row a c ↔ c = false := by
  rw [row_comp_iff]
  constructor
  · rintro ⟨_,h⟩
    let G (y : Middle) (v : Bool) := continuation y = v
    have hg : Difunctional G := fun _ _ _ _ h₁ h₂ h₃ => h₁.trans (h₂.symm.trans h₃)
    have edges : ∀ y v, expanded (fine.middle (pure continuation)) (pure continuation).selected (pure continuation).block y v → G y v := by
      rintro y v ⟨e,rfl,rfl⟩
      rfl
    exact (h G hg edges).symm
  · rintro rfl
    exact ⟨trivial, closure_extensive _ ⟨⟨Middle.zero,trivial⟩,rfl,rfl⟩⟩

theorem coarse_after (a : Unit) (c : Bool) : (coarse.comp (pure continuation)).row a c := by
  apply (row_comp_iff _ _ _ _).mpr
  refine ⟨trivial, ?_⟩
  intro R hR hEdges
  have edge (b : Middle) : R (coarsen b) (continuation b) :=
    hEdges _ _ ⟨⟨b,trivial⟩,rfl,rfl⟩
  cases c with
  | false => exact edge .zero
  | true => exact hR (edge .zero) (edge .one) (edge .two)

theorem partial_recipe_nondescent :
    ¬ ∃ F : (Unit → Middle → Prop) → (Unit → Bool → Prop),
      F fine.row = (fine.comp (pure continuation)).row ∧ F coarse.row = (coarse.comp (pure continuation)).row := by
  rintro ⟨F,hf,hc⟩
  have eq := hf.symm.trans ((congrArg F same_observation).trans hc)
  have h : (fine.comp (pure continuation)).row () true := eq ▸ coarse_after () true
  exact Bool.noConfusion ((fine_after () true).mp h)

end ContextualComposition.FiniteRelationForgetting
