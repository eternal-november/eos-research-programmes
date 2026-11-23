module
public import ContextualComposition.RelativeTensorTriangleAssembly
public import ContextualComposition.RelativeTensorTriangleLeftRoute

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.UnitTriangle
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{max u v uX vX,max u v uX}) (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vY uY,max u v uY})
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 20000

/-- Assign an already elaborated local proof. Lean checks the resulting declaration in the kernel. This avoids repeating dependent endpoint conversion for the nested tensor routes. -/
local elab "exactLocalProof " h:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let some decl := (← Lean.getLCtx).findFromUserName? h.getId | throwError "unknown local proof {h}"
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.assign decl.toExpr
  Lean.Elab.Tactic.replaceMainGoal []

theorem left_vertex (z : Left X (unitModule B) Y) :
    (lambdaRoute.{v,u,max u v uX vX,max u v uX,vY,uY} X Y).obj z =
      leftPoint.{v,u,vX,uX,max u v vY uY,max u v uY} X Y z := by
  obtain ⟨⟨j,⟨⟨i,x,⟨p⟩⟩⟩,y⟩⟩ := z
  rfl

/-- The source, inner-balance and outer-balance images of the actual left unitor route. -/
theorem left_images : LeftGeneratorImages.{v,u,vX,uX,max u v vY uY,max u v uY} X Y (lambdaRoute.{v,u,max u v uX vX,max u v uX,vY,uY} X Y) where
  native := by
    intro i j p x x' y y' f g
    have generator := heq_of_eq (lambda_native.{v,u,max u v uX vX,max u v uX,vY,uY} X Y p f g)
    exactLocalProof generator
  inner := by
    intro i j k u' p x y
    have generator := heq_of_eq (lambda_inner.{v,u,max u v uX vX,max u v uX,vY,uY} X Y u' p x y)
    exactLocalProof generator
  outer := by
    intro i j k p v' x y
    have generator := heq_of_eq (lambda_outer.{v,u,max u v uX vX,max u v uX,vY,uY} X Y p v' x y)
    exactLocalProof generator

/-- The actual associator/left-unitor route and the indexed right-unitor route are naturally isomorphic on the whole weak tensor. -/
def triangle : lambdaRoute.{v,u,max u v uX vX,max u v uX,vY,uY} X Y ≅ rhoRoute.{v,u,vX,uX,max u v vY uY,max u v uY} X Y :=
  ofLeftImages.{v,u,vX,uX,max u v vY uY,max u v uY} X Y _ (left_vertex.{v,u,vX,uX,vY,uY} X Y) (left_images.{v,u,vX,uX,vY,uY} X Y)

/-- The triangle comparison at each vertex is the original invertible balance at its hom label. -/
theorem triangle_app (z : Left X (unitModule B) Y) :
    (triangle.{v,u,vX,uX,vY,uY} X Y).hom.app z =
      (balancing X Y z.as.first.as.second.as z.as.first.as.first z.as.second).hom := by
  have h := ofLeftImages_app.{v,u,vX,uX,max u v vY uY,max u v uY} X Y _ (left_vertex.{v,u,vX,uX,vY,uY} X Y) (left_images.{v,u,vX,uX,vY,uY} X Y) z
  refine h.trans ?_
  obtain ⟨⟨j,⟨⟨i,x,⟨p⟩⟩⟩,y⟩⟩ := z
  exact Category.id_comp _

end ContextualComposition.RelativeTensor.Iterated.UnitTriangle
