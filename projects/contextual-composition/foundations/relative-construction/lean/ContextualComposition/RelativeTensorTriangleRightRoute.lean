module
public import ContextualComposition.RelativeTensorIndexedRightUnitor
public import ContextualComposition.RelativeTensorTriangleBalances

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.UnitTriangle
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{max u v uX vX,max u v uX}) (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- The triangle route evaluating the covariant factor at the hom label of the middle object. -/
abbrev rhoRoute := mapFirst (G := Y) (RightUnit.indexed.{v,u,vX,uX} X)

theorem rho_port {i j k : B} (p : i ⟶ j) (v' : j ⟶ k) (x : X.obj ⟨i⟩) :
    (First.port (RightUnit.indexed.{v,u,vX,uX} X) v' ((insertion X (RightUnit.represented j) i).obj (x,Discrete.mk p))).hom =
      (X.mapComp p.toLoc v'.toLoc).inv.toNatTrans.app x := by
  change (X.mapComp p.toLoc v'.toLoc).inv.toNatTrans.app x ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem rho_native {i j : B} (p : i ⟶ j) {x x' : X.obj ⟨i⟩} {y y' : Y.obj ⟨op j⟩} (f : x ⟶ x') (g : y ⟶ y') :
    (rhoRoute.{v,u,vX,uX,vY,uY} X Y).map ((Reverse.insertL X (unitModule B) Y j).map
      (productMap ((insertion X (RightUnit.represented j) i).map (productMap f (𝟙 (Discrete.mk p)))) g)) =
      (insertion X Y j).map (productMap ((forward X p).map f) g) := by
  unfold rhoRoute
  rw [First.on_native]
  change (insertion X Y j).map (productMap ((RightUnit.evaluation j X).map _) g) = _
  rw [RightUnit.eval_native]
  erw [eqToHom_refl,Category.comp_id]

theorem rho_inner {i j k : B} (u' : i ⟶ j) (p : j ⟶ k) (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :
    (rhoRoute.{v,u,vX,uX,vY,uY} X Y).map ((Reverse.insertL X (unitModule B) Y k).map
      (productMap (balancing X (RightUnit.represented k) u' x (Discrete.mk p)).hom (𝟙 y))) =
      (insertion X Y k).map (productMap ((X.mapComp u'.toLoc p.toLoc).hom.toNatTrans.app x) (𝟙 y)) := by
  unfold rhoRoute
  rw [First.on_native]
  change (insertion X Y k).map (productMap ((RightUnit.evaluation k X).map _) (𝟙 y)) = _
  rw [RightUnit.eval_balance]
  rfl

theorem rho_outer {i j k : B} (p : i ⟶ j) (v' : j ⟶ k) (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :
    (rhoRoute.{v,u,vX,uX,vY,uY} X Y).map (balancing (leftInner X (unitModule B)) Y v'
      ((insertion X (RightUnit.represented j) i).obj (x,Discrete.mk p)) y).hom =
      (balancing X Y v' ((forward X p).obj x) y).hom ≫ (insertion X Y k).map (productMap ((X.mapComp p.toLoc v'.toLoc).inv.toNatTrans.app x) (𝟙 y)) := by
  unfold rhoRoute
  rw [First.on_balance,rho_port]
  rfl

end ContextualComposition.RelativeTensor.Iterated.UnitTriangle
