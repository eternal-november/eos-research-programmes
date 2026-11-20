module
public import ContextualComposition.ContentRepresentable
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentCompositionCells
open CategoryTheory CategoryTheory.Bicategory Opposite
open RepresentableBicategoryAssembly
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {B : Type u} {H : B → B → Type v} [∀ x y, Category.{w} (H x y)]
variable (O : Operations H) (L : Laws O)
local notation "CB" => (build (ContentCoBicategory.ops O) (ContentCoBicategory.laws O L))

abbrev view {x y : B} (f : H y x) : @Quiver.Hom Bᵒᵖ (@Bicategory.Opposite.bicategory B CB).toQuiver (op x) (op y) :=
  letI : Bicategory B := CB
  Quiver.Hom.op (X := y) (Y := x) (op f)

abbrev viewCell {x y : B} {f f' : H y x} (t : f' ⟶ f) :
    letI : Bicategory B := CB
    view O L f ⟶ view O L f' :=
  letI : Bicategory B := CB
  Bicategory.Opposite.op2 t.op

/-- For arbitrary 2-cells the reversed 1-cell composite has exactly the
reversed slot order and no additional cell reversal in the covariant chart. -/
theorem binaryMap {x y z : B} {f f' : H y x} {g g' : H z y}
    (t : f' ⟶ f) (s : g' ⟶ g) :
    letI : Bicategory B := CB
    ((RepresentableComparisonEquivalences.binary (op x) (op y) (op z)).map
      (X := (view O L f,view O L g)) (Y := (view O L f',view O L g'))
      (viewCell O L t,viewCell O L s)).unop2.unop = compCell O s t := by
  change rW O s f' ≫ lW O g t = compCell O s t
  rw [← cellComp,Category.comp_id,Category.id_comp]

end ContextualComposition.GrothendieckStep.ContentCompositionCells
