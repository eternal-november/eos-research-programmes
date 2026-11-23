module
public import ContextualComposition.RelativeTensorMiddleRow
public import ContextualComposition.RelativeTensorUnitRows
public import ContextualComposition.RelativeTensorRightContraction

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
universe v u vC uC vM uM
variable {B : Type u} [Category.{v} B] {C : Type uC} [Category.{vC} C]
variable {M N : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})}

private def rowCell {P Q : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}} {h k : P ⟶ Q}
    (a : B) (x : P.obj ⟨op a⟩) (m : h ⟶ k) := (m.as.app ⟨op a⟩).toNatTrans.app x

private theorem mapIdRow (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})) (a : B) (j : LocallyDiscrete C) (x : (row M a).obj j) :
    ((row M a).mapId j).hom.toNatTrans.app x = rowCell a x (M.mapId j).hom :=
  Category.comp_id _

private theorem mapCompRow (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})) (a : B) {i j k : LocallyDiscrete C}
    (f : i ⟶ j) (g : j ⟶ k) (x : (row M a).obj i) :
    ((row M a).mapComp f g).hom.toNatTrans.app x = rowCell a x (M.mapComp f g).hom :=
  Category.comp_id _

/-- Evaluate a supplied strong map of curried modules at a fixed first endpoint. -/
def rowMap (s : M ⟶ N) (a : B) : row M a ⟶ row N a where
  app j := (s.app j).app ⟨op a⟩
  naturality f := (Middle.evaluate (⟨op a⟩ : LocallyDiscrete Bᵒᵖ)).map₂Iso (s.naturality f)
  naturality_naturality η := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    exact congrArg (rowCell a x) (s.naturality_naturality η)
  naturality_id j := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    let S := ((s.app j).app ⟨op a⟩).toFunctor
    have h := congrArg (rowCell a x) (s.naturality_id j)
    change rowCell a x (s.naturality (𝟙 j)).hom ≫ rowCell a (S.obj x) (N.mapId j).hom =
      S.map (rowCell a x (M.mapId j).hom) ≫ 𝟙 _ ≫ 𝟙 _ at h
    change rowCell a x (s.naturality (𝟙 j)).hom ≫ ((row N a).mapId j).hom.toNatTrans.app (S.obj x) =
      S.map (((row M a).mapId j).hom.toNatTrans.app x) ≫ 𝟙 _ ≫ 𝟙 _
    rw [mapIdRow,mapIdRow]
    exact h
  naturality_comp {i j k} f g := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    let Si := ((s.app i).app ⟨op a⟩).toFunctor
    let Sk := ((s.app k).app ⟨op a⟩).toFunctor
    let Mf := ((M.map f).app ⟨op a⟩).toFunctor
    let Ng := ((N.map g).app ⟨op a⟩).toFunctor
    have h := congrArg (rowCell a x) (s.naturality_comp f g)
    change rowCell a x (s.naturality (f ≫ g)).hom ≫ rowCell a (Si.obj x) (N.mapComp f g).hom =
      Sk.map (rowCell a x (M.mapComp f g).hom) ≫ 𝟙 _ ≫ rowCell a (Mf.obj x) (s.naturality g).hom ≫ 𝟙 _ ≫
      Ng.map (rowCell a x (s.naturality f).hom) ≫ 𝟙 _ at h
    change rowCell a x (s.naturality (f ≫ g)).hom ≫ ((row N a).mapComp f g).hom.toNatTrans.app (Si.obj x) =
      Sk.map (((row M a).mapComp f g).hom.toNatTrans.app x) ≫ 𝟙 _ ≫ rowCell a (Mf.obj x) (s.naturality g).hom ≫ 𝟙 _ ≫
      Ng.map (rowCell a x (s.naturality f).hom) ≫ 𝟙 _
    rw [mapCompRow,mapCompRow]
    exact h

@[simp] theorem rowMap_app (s : M ⟶ N) (a : B) (j : LocallyDiscrete C) :
    (rowMap s a).app j = (s.app j).app ⟨op a⟩ := rfl

theorem rowMap_naturality (s : M ⟶ N) (a : B) {i j : LocallyDiscrete C} (f : i ⟶ j) :
    (rowMap s a).naturality f = (Middle.evaluate (⟨op a⟩ : LocallyDiscrete Bᵒᵖ)).map₂Iso (s.naturality f) := rfl

end ContextualComposition.RelativeTensor.Iterated
