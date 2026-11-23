module
public import ContextualComposition.RelativeTensorMiddleRow
public import ContextualComposition.RelativeTensorAssociatorFirstChange

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vM uM vN uN
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable {a b : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b)

theorem middleRow_change_app (d : LocallyDiscrete D) :
    (Middle.change (middleComposite M N) u).app d = (firstMap (Middle.change M u) N).app d := rfl

theorem middleRow_change_square {d e : LocallyDiscrete D} (v : d ⟶ e) :
    (Middle.change (middleComposite M N) u).naturality v = (firstMap (Middle.change M u) N).naturality v := rfl

private theorem strong_heq {A U : Type*} [Bicategory A] [Bicategory U]
    {F G F' G' : A ⥤ᵖ U} (s : F ⟶ G) (t : F' ⟶ G') (h : F = F') (k : G = G')
    (ha : HEq s.app t.app) (hn : HEq (@s.naturality) (@t.naturality)) : HEq s t := by
  subst F'; subst G'
  cases s; cases t; cases ha; cases hn; rfl

/-- In the first endpoint direction, the actual strong transition of the
middle composite is the first-factor map, including its interchange square. -/
theorem middleRow_change : HEq (Middle.change (middleComposite M N) u) (firstMap (Middle.change M u) N) :=
  strong_heq _ _ (middleRow M N a.as.unop) (middleRow M N b.as.unop) HEq.rfl HEq.rfl

section Tensor
universe vY uY

/-- Change the first action of a tensor along equality of the whole pseudofunctor. -/
def identifyFirst {F G : LocallyDiscrete D ⥤ᵖ Cat.{vN,uN}} (h : F = G) (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY}) :
    Tensor F Y ≌ Tensor G Y := by
  subst G
  exact CategoryTheory.Equivalence.refl

private theorem identifyFirst_square {F G F' G' : LocallyDiscrete D ⥤ᵖ Cat.{vN,uN}} (h : F = F') (k : G = G')
    (s : F ⟶ G) (t : F' ⟶ G') (e : HEq s t) (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY}) :
    mapFirst s ⋙ (identifyFirst k Y).functor = (identifyFirst h Y).functor ⋙ mapFirst t := by
  subst F'; subst G'
  cases eq_of_heq e
  exact (Functor.comp_id (mapFirst (G := Y) s)).trans (Functor.id_comp _).symm

variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

/-- The actual third-junction row equivalence, with input from the middle composite. -/
def rightRowAssociator (b : LocallyDiscrete Bᵒᵖ) :
    CategoryTheory.Equivalence ((rightInner (middleComposite M N) Y).obj b) ((rightInner M (rightInner N Y)).obj b) :=
  (identifyFirst (middleRow M N b.as.unop) Y).trans (associator (row M b.as.unop) N Y)

/-- Reindexing by the full row identification commutes with first-factor
change on the actual D-tensors. This is the square to paste with first_naturality. -/
theorem rightRow_change :
    mapFirst (Middle.change (middleComposite M N) u) ⋙ (identifyFirst (middleRow M N b.as.unop) Y).functor =
      (identifyFirst (middleRow M N a.as.unop) Y).functor ⋙ mapFirst (firstMap (Middle.change M u) N) :=
  identifyFirst_square (middleRow M N a.as.unop) (middleRow M N b.as.unop)
    (Middle.change (middleComposite M N) u) (firstMap (Middle.change M u) N) (middleRow_change M N u) Y

end Tensor

end ContextualComposition.RelativeTensor.Iterated
