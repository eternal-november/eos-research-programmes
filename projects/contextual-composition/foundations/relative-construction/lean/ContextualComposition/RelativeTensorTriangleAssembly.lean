module
public import ContextualComposition.RelativeTensorTriangleRightRoute

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.UnitTriangle
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{max u v uX vX,max u v uX}) (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- The left-route vertex coordinate before the single balance moving its hom label across the junction. -/
abbrev leftPoint (z : Left X (unitModule B) Y) :=
  (insertion X Y z.as.first.as.mid).obj (z.as.first.as.first,(backward Y z.as.first.as.second.as).obj z.as.second)

def vertexBalance (z : Left X (unitModule B) Y) :
    leftPoint.{v,u,vX,uX,vY,uY} X Y z ≅ (rhoRoute.{v,u,vX,uX,vY,uY} X Y).obj z :=
  balancing X Y z.as.first.as.second.as z.as.first.as.first z.as.second

variable (H : Left X (unitModule B) Y ⥤ Tensor X Y)
variable (o : ∀ z, H.obj z = leftPoint.{v,u,vX,uX,vY,uY} X Y z)

/-- Rebracket and evaluate on the left; only the three generator images, before comparison with the right route, are required. -/
structure LeftGeneratorImages : Prop where
  native {i j : B} (p : i ⟶ j) {x x' : X.obj ⟨i⟩} {y y' : Y.obj ⟨op j⟩} (f : x ⟶ x') (g : y ⟶ y') :
    HEq (H.map ((Reverse.insertL X (unitModule B) Y j).map
      (productMap ((insertion X (RightUnit.represented j) i).map (productMap f (𝟙 (Discrete.mk p)))) g)))
      ((insertion X Y i).map (productMap f ((backward Y p).map g)))
  inner {i j k : B} (u' : i ⟶ j) (p : j ⟶ k) (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :
    HEq (H.map ((Reverse.insertL X (unitModule B) Y k).map (productMap (balancing X (RightUnit.represented k) u' x (Discrete.mk p)).hom (𝟙 y))))
      ((insertion X Y i).map (productMap (𝟙 x) ((Y.mapComp p.op.toLoc u'.op.toLoc).hom.toNatTrans.app y)) ≫
        (balancing X Y u' x ((backward Y p).obj y)).hom)
  outer {i j k : B} (p : i ⟶ j) (v' : j ⟶ k) (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :
    HEq (H.map (balancing (leftInner X (unitModule B)) Y v' ((insertion X (RightUnit.represented j) i).obj (x,Discrete.mk p)) y).hom)
      ((insertion X Y i).map (productMap (𝟙 x) ((Y.mapComp v'.op.toLoc p.op.toLoc).inv.toNatTrans.app y)))

private theorem transported {T : Type*} [Category* T] {a b a' b' c d : T} (e : a = a') (e' : b = b')
    (j : a' ≅ c) (k : b' ≅ d) (f : a ⟶ b) (f' : a' ⟶ b') (g g' : c ⟶ d) (hf : HEq f f') (hg : g = g')
    (w : f' ≫ k.hom = j.hom ≫ g') : f ≫ (eqToIso e' ≪≫ k).hom = (eqToIso e ≪≫ j).hom ≫ g := by
  subst a'; subst b'; subst g'
  cases eq_of_heq hf
  simpa only [eqToIso_refl,Iso.refl_trans] using w

private theorem compareGenerator {z w : Left X (unitModule B) Y} (f : z ⟶ w)
    (h : leftPoint.{v,u,vX,uX,vY,uY} X Y z ⟶ leftPoint.{v,u,vX,uX,vY,uY} X Y w)
    (k : (rhoRoute.{v,u,vX,uX,vY,uY} X Y).obj z ⟶ (rhoRoute.{v,u,vX,uX,vY,uY} X Y).obj w)
    (hh : HEq (H.map f) h) (hk : (rhoRoute.{v,u,vX,uX,vY,uY} X Y).map f = k)
    (sq : h ≫ (vertexBalance.{v,u,vX,uX,vY,uY} X Y w).hom = (vertexBalance.{v,u,vX,uX,vY,uY} X Y z).hom ≫ k) :
    CompareAt (H := H) (K := rhoRoute.{v,u,vX,uX,vY,uY} X Y) (fun z => eqToIso (o z) ≪≫ vertexBalance.{v,u,vX,uX,vY,uY} X Y z) f :=
  transported (o z) (o w) _ _ (H.map f) h _ k hh hk sq

/-- The three left images satisfy the triangle generator tests against the actual right route. -/
theorem lawsOfLeftImages (h : LeftGeneratorImages.{v,u,vX,uX,vY,uY} X Y H) :
    GeneratorLaws X Y (H := H) (K := rhoRoute.{v,u,vX,uX,vY,uY} X Y) (fun z => eqToIso (o z) ≪≫ vertexBalance.{v,u,vX,uX,vY,uY} X Y z) := by
  constructor
  · intro i j p x x' y y' f g
    exact compareGenerator.{v,u,vX,uX,vY,uY} X Y H o _ _ _ (h.native p f g) (rho_native.{v,u,vX,uX,vY,uY} X Y p f g) (native_square X Y p f g)
  · intro i j k u' p x y
    exact compareGenerator.{v,u,vX,uX,vY,uY} X Y H o _ _ _ (h.inner u' p x y) (rho_inner.{v,u,vX,uX,vY,uY} X Y u' p x y) (inner_square X Y u' p x y)
  · intro i j k p v' x y
    exact compareGenerator.{v,u,vX,uX,vY,uY} X Y H o _ _ _ (h.outer p v' x y) (rho_outer.{v,u,vX,uX,vY,uY} X Y p v' x y) (outer_square X Y p v' x y)

/-- The native balancing isomorphisms at the hom labels assemble to a natural isomorphism on every quotient path. -/
def ofLeftImages (h : LeftGeneratorImages.{v,u,vX,uX,vY,uY} X Y H) : H ≅ rhoRoute.{v,u,vX,uX,vY,uY} X Y :=
  assemble X Y _ (lawsOfLeftImages.{v,u,vX,uX,vY,uY} X Y H o h)

theorem ofLeftImages_app (h : LeftGeneratorImages.{v,u,vX,uX,vY,uY} X Y H) (z : Left X (unitModule B) Y) :
    (ofLeftImages.{v,u,vX,uX,vY,uY} X Y H o h).hom.app z =
      eqToHom (o z) ≫ (balancing X Y z.as.first.as.second.as z.as.first.as.first z.as.second).hom := rfl

end ContextualComposition.RelativeTensor.Iterated.UnitTriangle
