module
public import ContextualComposition.RepresentableComparisonTransport
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableComparisonEquivalences
open CategoryTheory CategoryTheory.Bicategory
open RepresentableComparisonTransport
open RepresentableKleisli (horizontal horizontal_id horizontal_comp)
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v w z q
variable {B : Type u} [Bicategory.{w,v} B] {H : B → B → Type z} [∀ x y, Category.{q} (H x y)]
def binary (x y z : B) : (x ⟶ y) × (y ⟶ z) ⥤ (x ⟶ z) where
  obj t := t.1 ≫ t.2
  map t := horizontal t.1 t.2
  map_id _ := horizontal_id
  map_comp t q := horizontal_comp t.1 q.1 t.2 q.2
variable (E : ∀ x y : B, H x y ≌ (x ⟶ y))
def comp {x y z : B} :=
  ((E x y).functor.prod (E y z).functor) ⋙ binary x y z ⋙ (E x z).inverse
def unit (x : B) := (E x x).inverse.obj (𝟙 x)
set_option warn.classDefReducibility false in
def data : Data H where
  unit := unit E
  mult := fun {_ _ _} => comp E
  hom := fun x y => (E x y).functor
  fullfaithful := fun x y => (E x y).fullyFaithfulFunctor
  unitIso x := (E x x).counitIso.app _
  cmpIso := fun {x _ z} _ _ => (E x z).counitIso.app _
  cmpNat := by
    intro x y z f f' g g' s t
    exact (E x z).counitIso.hom.naturality (horizontal ((E x y).functor.map s) ((E y z).functor.map t))
end ContextualComposition.GrothendieckStep.RepresentableComparisonEquivalences
