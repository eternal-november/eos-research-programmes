module
public import ContextualComposition.RelativeTensorAssociatorFirstChange

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory CategoryTheory.Functor Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable {X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} {s t : X ⟶ X'} (m : s ⟶ t)
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

private theorem interchange_inv (s : X ⟶ X') {G H : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}} (v : G ⟶ H) (x : Tensor X G) :
    (Parametric.interchange s v).inv.toNatTrans.app x = 𝟙 _ := by
  change (eqToHom (factor_order s v).symm).app x = 𝟙 _
  rw [eqToHom_app]; rfl

/-- A directed first-factor modification acts on each binary tensor by its existing first-factor modification. -/
def varyFirstCell : varyFirst.{vB,uB,vX,uX,vM,uM} s ⟶ varyFirst t where
  as := {
    app _ := (First.mapCell m.as).toCatHom₂
    naturality := by
      intro A D v
      apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
      change (First.mapCell (G := D) m.as).app ((mapSecond (F := X) v).obj x) ≫ (Parametric.interchange t v).inv.toNatTrans.app x =
        (Parametric.interchange s v).inv.toNatTrans.app x ≫ (mapSecond (F := X') v).map ((First.mapCell (G := A) m.as).app x)
      erw [interchange_inv,interchange_inv,Category.comp_id,Category.id_comp,First.cell_app,First.cell_app,Second.on_native,Functor.map_id]
      rfl }

/-- Evaluate the directed first-factor modification on all columns of the weak middle module. -/
def firstMapCell : firstMap s M ⟶ firstMap t M := Factorization.Endpoint.Indexed.reindexCell M (varyFirstCell m)

theorem first_cell_app (z : Left X M Y) :
    (associate X' M Y).map ((First.mapCell (G := Y) (firstMapCell m M).as).app z) =
      (First.mapCell (G := rightInner M Y) m.as).app ((associate X M Y).obj z) := by
  obtain ⟨⟨c,⟨⟨b,x,k⟩⟩,y⟩⟩ := z
  exact associate_leaf X' M Y ((insertM M Y b c).obj (k,y)) ((m.as.app ⟨b⟩).toNatTrans.app x)

private theorem first_transport (s : X ⟶ X') (z : Left X M Y) :
    (eqToHom (first_naturality s M Y)).app z = 𝟙 _ := by rw [eqToHom_app]; rfl

/-- The two boundary equalities of first-factor associator naturality intertwine the induced directed modifications on the entire tensor. -/
theorem first_modification :
    whiskerRight (First.mapCell (G := Y) (firstMapCell m M).as) (associate X' M Y) ≫ eqToHom (first_naturality t M Y) =
      eqToHom (first_naturality s M Y) ≫ whiskerLeft (associate X M Y) (First.mapCell (G := rightInner M Y) m.as) := by
  apply NatTrans.ext
  funext z
  simpa only [NatTrans.comp_app,whiskerLeft_app,whiskerRight_app,first_transport,Category.comp_id,Category.id_comp] using first_cell_app m M Y z

section Constraints
universe uA vA wA
variable {A : Type uA} [Bicategory.{wA,vA} A]
variable (F : A ⥤ᵖ (LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})) (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})

private theorem actionUnit (a : A) (z : Tensor (F.obj a) G) :
    (First.mapCell (G := G) (F.mapId a).hom.as).app z = ((F.comp (First.action G)).mapId a).hom.toNatTrans.app z := by
  change _ = _ ≫ (First.identityIso G (F.obj a)).hom.toNatTrans.app z
  rw [First.identity_hom_app]
  exact (Category.comp_id _).symm

private theorem actionComp {a b c : A} (u : a ⟶ b) (v : b ⟶ c) (z : Tensor (F.obj a) G) :
    (First.mapCell (G := G) (F.mapComp u v).hom.as).app z = ((F.comp (First.action G)).mapComp u v).hom.toNatTrans.app z := by
  change _ = _ ≫ (First.compositeIso G (F.map u) (F.map v)).hom.toNatTrans.app z
  rw [First.composite_hom_app]
  exact (Category.comp_id _).symm

end Constraints

section Rows
universe vD uD vN uN vW uW
variable {D : Type uD} [Category.{vD} D]
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (W : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vW,uW})

/-- At an actual row, the first-factor lift of the transpose's unitor is carried to the right-inner action's native unit component. -/
theorem first_row_unit (b : LocallyDiscrete Bᵒᵖ) (z : Left (Middle.atIndex M b) N W) :
    (associate (Middle.atIndex M b) N W).map ((First.mapCell (G := W) (firstMapCell (Middle.changeUnit M b).hom N).as).app z) =
      ((rightInner M (rightInner N W)).mapId b).hom.toNatTrans.app ((associate (Middle.atIndex M b) N W).obj z) := by
  exact (first_cell_app (Middle.changeUnit M b).hom N W z).trans
    (actionUnit (Middle.transpose M) (rightInner N W) b ((associate (Middle.atIndex M b) N W).obj z))

/-- At composable row changes the same calculation gives the native compositor component of the right-inner action. -/
theorem first_row_compositor {a b c : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b) (v : b ⟶ c) (z : Left (Middle.atIndex M a) N W) :
    (associate (Middle.atIndex M c) N W).map ((First.mapCell (G := W) (firstMapCell (Middle.changeComposition M u v).hom N).as).app z) =
      ((rightInner M (rightInner N W)).mapComp u v).hom.toNatTrans.app ((associate (Middle.atIndex M a) N W).obj z) := by
  exact (first_cell_app (Middle.changeComposition M u v).hom N W z).trans
    (actionComp (Middle.transpose M) (rightInner N W) u v ((associate (Middle.atIndex M a) N W).obj z))

end Rows

end ContextualComposition.RelativeTensor.Iterated
