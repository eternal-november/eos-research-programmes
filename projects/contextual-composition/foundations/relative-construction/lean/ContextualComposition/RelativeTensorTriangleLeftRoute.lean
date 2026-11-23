module
public import ContextualComposition.RelativeTensorCurriedLeftUnitor
public import ContextualComposition.RelativeTensorTriangleBalances
public import ContextualComposition.RelativeTensorFourNative
public import ContextualComposition.RelativeTensorFourBalanceB

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.UnitTriangle
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
universe v u vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vY uY,max u v uY})
/-- Reassociate, then evaluate the contravariant factor at the represented arrow. -/
abbrev lambdaRoute := associate X (unitModule B) Y ⋙ mapSecond (F := X) (leftUnitor.{v,u,vY,uY} Y)

theorem lambda_native {i j : B} (p : i ⟶ j) {x x' : X.obj ⟨i⟩} {y y' : Y.obj ⟨op j⟩} (f : x ⟶ x') (g : y ⟶ y') :
    (lambdaRoute.{v,u,vX,uX,vY,uY} X Y).map ((Reverse.insertL X (unitModule B) Y j).map
      (productMap ((insertion X (RightUnit.represented j) i).map (productMap f (𝟙 (Discrete.mk p)))) g)) =
      (insertion X Y i).map (productMap f ((backward Y p).map g)) := by
  rw [Functor.comp_map]
  erw [associate_triple_native X (unitModule B) Y f (𝟙 (Discrete.mk p)) g,Second.on_native,leftUnitor_native]

theorem lambda_inner {i j k : B} (u' : i ⟶ j) (p : j ⟶ k) (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :
    (lambdaRoute.{v,u,vX,uX,vY,uY} X Y).map ((Reverse.insertL X (unitModule B) Y k).map
      (productMap (balancing X (RightUnit.represented k) u' x (Discrete.mk p)).hom (𝟙 y))) =
      (insertion X Y i).map (productMap (𝟙 x) ((Y.mapComp p.op.toLoc u'.op.toLoc).hom.toNatTrans.app y)) ≫
        (balancing X Y u' x ((backward Y p).obj y)).hom := by
  rw [Functor.comp_map]
  erw [associate_inner_slide X (unitModule B) Y u' x (Discrete.mk p) y,Second.on_balance,leftUnitor_port]
  rfl

theorem lambda_outer {i j k : B} (p : i ⟶ j) (v' : j ⟶ k) (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :
    (lambdaRoute.{v,u,vX,uX,vY,uY} X Y).map (balancing (leftInner X (unitModule B)) Y v'
      ((insertion X (RightUnit.represented j) i).obj (x,Discrete.mk p)) y).hom =
      (insertion X Y i).map (productMap (𝟙 x) ((Y.mapComp v'.op.toLoc p.op.toLoc).inv.toNatTrans.app y)) := by
  rw [Functor.comp_map,associate_outer_balance]
  change (mapSecond (F := X) (leftUnitor.{v,u,vY,uY} Y)).map ((insertion X (rightInner (unitModule B) Y) i).map
    (productMap (𝟙 x) (balancing (row (unitModule B) i) Y v' (Discrete.mk p) y).hom)) = _
  rw [Second.on_native,leftUnitor_balance]

end ContextualComposition.RelativeTensor.Iterated.UnitTriangle
