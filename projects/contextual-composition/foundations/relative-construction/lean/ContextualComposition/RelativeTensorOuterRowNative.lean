module
public import ContextualComposition.RelativeTensorOuterRowIdentity
public import ContextualComposition.RelativeTensorAssociatorFirstCell

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.OuterRow
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

theorem columnUnit (b : LocallyDiscrete Bᵒᵖ) (d : D) (p : Tensor (row M b.as.unop) (column N d)) :
    (((middleComposite M N).obj ⟨d⟩).mapId b).hom.toNatTrans.app p =
      (First.mapCell (G := column N d) (Middle.changeUnit M b).hom.as).app p := by
  change _ ≫ (First.identityIso (column N d) (row M b.as.unop)).hom.toNatTrans.app p = _
  rw [First.identity_hom_app]
  exact Category.comp_id ((First.mapCell (G := column N d) (Middle.changeUnit M b).hom.as).app p)

theorem columnComp {a b c : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b) (v : b ⟶ c) (d : D)
    (p : Tensor (row M a.as.unop) (column N d)) :
    (((middleComposite M N).obj ⟨d⟩).mapComp u v).hom.toNatTrans.app p =
      (First.mapCell (G := column N d) (Middle.changeComposition M u v).hom.as).app p := by
  change _ ≫ (First.compositeIso (column N d) (Middle.change M u) (Middle.change M v)).hom.toNatTrans.app p = _
  rw [First.composite_hom_app,Category.comp_id]
  rfl

theorem normalize_unit (b : LocallyDiscrete Bᵒᵖ) (z : source M N Y b) :
    (mapFirst (G := Y) (rowId M N b)).map (((rightInner (middleComposite M N) Y).mapId b).hom.toNatTrans.app z) =
      (First.mapCell (G := Y) (firstMapCell (Middle.changeUnit M b).hom N).as).app ((mapFirst (G := Y) (rowId M N b)).obj z) := by
  obtain ⟨⟨d,p,y⟩⟩ := z
  have hu := right_unit (b := b.as.unop) (middleComposite M N) Y d p y
  refine (congrArg (mapFirst (G := Y) (rowId M N b)).map hu).trans ?_
  rw [First.on_native]
  change (insertion (leftInner (row M b.as.unop) N) Y d).map (productMap _ (𝟙 y)) = _
  rw [columnUnit M N b d p]
  rfl

def atVertex {F : LocallyDiscrete D ⥤ᵖ Cat.{vM,uM}} (d : D) {p q : F.obj ⟨d⟩}
    (y : Y.obj ⟨op d⟩) (m : p ⟶ q) := (insertion F Y d).map (productMap m (𝟙 y))

theorem rowNative (c : LocallyDiscrete Bᵒᵖ) (d : D) {p q : Tensor (row M c.as.unop) (column N d)}
    (y : Y.obj ⟨op d⟩) (m : p ⟶ q) :
    (mapFirst (G := Y) (rowId M N c)).map (atVertex (F := row (middleComposite M N) c.as.unop) Y d y m) =
      atVertex (F := leftInner (row M c.as.unop) N) Y d y m :=
  First.on_native (rowId M N c) m (𝟙 y)

universe vT uT

theorem source_comp_vertex (T : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vT,uT}))
    {a b c : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b) (v : b ⟶ c) (z : Tensor (row T a.as.unop) Y) :
    ((rightInner T Y).mapComp u v).hom.toNatTrans.app z =
      atVertex (F := row T c.as.unop) Y z.as.mid z.as.second
        (((T.obj ⟨z.as.mid⟩).mapComp u v).hom.toNatTrans.app z.as.first) := by
  change (First.mapCell (G := Y) (Middle.changeComposition T u v).hom.as).app z ≫
    (First.compositeIso Y (Middle.change T u) (Middle.change T v)).hom.toNatTrans.app z = _
  rw [First.composite_hom_app]
  exact Category.comp_id ((First.mapCell (G := Y) (Middle.changeComposition T u v).hom.as).app z)

end ContextualComposition.RelativeTensor.Iterated.OuterRow
