module
public import ContextualComposition.RelativeTensorUniversal
public import ContextualComposition.CommaCoconeComparison
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

@[expose] public section
namespace ContextualComposition.RelativeTensor.Presented
open CategoryTheory Opposite Factorization
open scoped CategoryTheory.Bicategory
universe vK vL vC vD uK uL uC uD
variable {K : Type uK} {L : Type uL} {C : Type uC} {D : Type uD}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vC} C] [Category.{vD} D]
variable (e : K ⥤ C) (d : L ⥤ C)
set_option backward.isDefEq.respectTransparency false

abbrev input := (CostructuredArrow.functor e).toPseudofunctor'
abbrev output := (StructuredArrow.functor d).toPseudofunctor'

theorem input_unit {i : C} (x : CostructuredArrow e i) :
    (((input e).mapId ⟨i⟩).inv.toNatTrans.app x).left = 𝟙 x.left := by
  simp only [input, Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]
  exact CostructuredArrow.eqToHom_left (X := x) (Y := (CostructuredArrow.map (𝟙 i)).obj x) _

theorem output_unit {i : C} (y : StructuredArrow i d) :
    (((output d).mapId ⟨op i⟩).hom.toNatTrans.app y).right = 𝟙 y.right := by
  simp only [output, Functor.toPseudofunctor'_mapId, eqToIso.hom, Cat.eqToHom_app]
  exact StructuredArrow.eqToHom_right (X := (StructuredArrow.map (𝟙 i)).obj y) (Y := y) _

theorem input_comp {i j k : C} (u : i ⟶ j) (v : j ⟶ k) (x : CostructuredArrow e i) :
    (((input e).mapComp u.toLoc v.toLoc).inv.toNatTrans.app x).left = 𝟙 x.left := by
  simp only [input, Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app]
  exact CostructuredArrow.eqToHom_left (X := (CostructuredArrow.map v).obj ((CostructuredArrow.map u).obj x))
    (Y := (CostructuredArrow.map (u ≫ v)).obj x) _

theorem output_comp {i j k : C} (u : i ⟶ j) (v : j ⟶ k) (y : StructuredArrow k d) :
    (((output d).mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app y).right = 𝟙 y.right := by
  simp only [output, Functor.toPseudofunctor'_mapComp, eqToIso.hom, Cat.eqToHom_app]
  exact StructuredArrow.eqToHom_right (X := (StructuredArrow.map (u ≫ v)).obj y)
    (Y := (StructuredArrow.map u).obj ((StructuredArrow.map v).obj y)) _

/-- Read the comma presentation's native fixed-middle product arrows and balancing isomorphisms into the generic cocone interface. -/
def read (S : Source.Cocone e d (D := D)) : Cocone (input e) (output d) D where
  fiber := Source.fibreFunctor e d S
  bal u x y := S.bal x.hom u y.hom
  natural := by
    intro i j u x x' y y' p q
    exact S.bal_natural x.hom x'.hom u y.hom y'.hom p.left q.right (CostructuredArrow.w p) (StructuredArrow.w q)
  unit {i} x y := by
    rw [S.bal_id]
    apply congrArg (fun f => S.map f)
    apply Source.ProductHom.ext
    · exact (input_unit e x).symm
    · exact (output_unit d y).symm
  comp u v x y := by
    rw [S.bal_comp]
    congr 1
    · apply congrArg (fun h => S.map h)
      apply Source.ProductHom.ext
      · rfl
      · exact (output_comp d u v y).symm
    · congr 1
      congr 1
      apply congrArg (fun h => S.map h)
      apply Source.ProductHom.ext
      · exact (input_comp e u v x).symm
      · rfl

def readCell {S T : Source.Cocone e d (D := D)} (m : S ⟶ T) : read e d S ⟶ read e d T where
  components _ := {
    app := fun x => m.app (Source.fibreObject e d x)
    naturality := fun _ _ f => m.native_naturality (Source.fibreProduct e d f) }
  square u x y := m.balance_naturality x.hom u y.hom

def readFunctor : Source.Cocone e d (D := D) ⥤ Cocone (input e) (output d) D where
  obj := read e d
  map := readCell e d
  map_id _ := rfl
  map_comp _ _ := rfl

end ContextualComposition.RelativeTensor.Presented
