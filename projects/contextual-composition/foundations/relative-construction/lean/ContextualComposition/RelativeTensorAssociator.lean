module
public import ContextualComposition.RelativeTensorRebracketingRecovery

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

private theorem pad {D : Type*} [Category* D] {a b : D} {f g : a ⟶ b} (h : f = g) : f ≫ 𝟙 _ = 𝟙 _ ≫ g := by simpa using h

theorem restore_left_native {c : C} {p p' : Tensor X (column M c)} {y y' : Y.obj ⟨op c⟩} (f : p ⟶ p') (g : y ⟶ y') :
    (Reverse.unassociate X M Y).map ((outerFiber X M Y c).map (productMap f g)) =
      (Reverse.insertL X M Y c).map (productMap f g) := by
  have h := Functor.congr_hom (left_inner_recover X M Y y') f
  change (Reverse.unassociate X M Y).map ((innerCocone X M Y c y').extend.map f) = 𝟙 _ ≫ (Reverse.keep X M Y y').map f ≫ 𝟙 _ at h
  erw [Category.id_comp,Category.comp_id] at h
  rw [outer_pair,Functor.map_comp,unassociate_leaf,h]
  change (Reverse.insertL X M Y c).map (productMap (𝟙 p) g) ≫ (Reverse.insertL X M Y c).map (productMap f (𝟙 y')) = _
  rw [← Functor.map_comp]
  exact congrArg (Reverse.insertL X M Y c).map (Prod.ext (Category.id_comp _) (Category.comp_id _))

theorem restore_right_native {b : B} {x x' : X.obj ⟨b⟩} {p p' : Tensor (row M b) Y} (f : x ⟶ x') (g : p ⟶ p') :
    (associate X M Y).map ((Reverse.outerFiber X M Y b).map (productMap f g)) =
      (insertR X M Y b).map (productMap f g) := by
  have h := Functor.congr_hom (right_inner_recover X M Y x') g
  change (associate X M Y).map ((Reverse.innerCocone X M Y x').extend.map g) = 𝟙 _ ≫ (keep X M Y x').map g ≫ 𝟙 _ at h
  erw [Category.id_comp,Category.comp_id] at h
  rw [Reverse.outer_pair,Functor.map_comp,associate_leaf,h]
  change (insertR X M Y b).map (productMap f (𝟙 p)) ≫ (insertR X M Y b).map (productMap (𝟙 x') g) = _
  rw [← Functor.map_comp]
  exact congrArg (insertR X M Y b).map (Prod.ext (Category.comp_id _) (Category.id_comp _))

theorem restore_left_balance {c d : C} (v : c ⟶ d) (z : Tensor X (column M c)) (y : Y.obj ⟨op d⟩) :
    (Reverse.unassociate X M Y).map (outerComponent X M Y v y z).hom = (balancing (leftInner X M) Y v z y).hom := by
  obtain ⟨⟨b,x,m⟩⟩ := z
  change (Reverse.unassociate X M Y).map ((insertR X M Y b).map (productMap (𝟙 x) (balancing (row M b) Y v m y).hom)) = _
  rw [unassociate_native,reverse_only_inner,Reverse.inner_balance]
  rfl

theorem restore_right_balance {a b : B} (u : a ⟶ b) (x : X.obj ⟨a⟩) (z : Tensor (row M b) Y) :
    (associate X M Y).map (Reverse.outerComponent X M Y u x z).hom = (balancing X (rightInner M Y) u x z).hom := by
  obtain ⟨⟨c,m,y⟩⟩ := z
  change (associate X M Y).map ((Reverse.insertL X M Y c).map (productMap (balancing X (column M c) u x m).hom (𝟙 y))) = _
  rw [associate_native,outer_only_inner,inner_balance]
  rfl

theorem roundtrip_left : associate X M Y ⋙ Reverse.unassociate X M Y = 𝟭 (Left X M Y) := by
  fapply extGenerators
  · intro z; rfl
  · intro c p p' y y' f g
    apply pad
    dsimp only [Functor.comp_map]
    rw [associate_native]
    exact restore_left_native X M Y f g
  · intro c d v p y
    apply pad
    dsimp only [Functor.comp_map]
    rw [associate_outer_balance]
    exact restore_left_balance X M Y v p y

theorem roundtrip_right : Reverse.unassociate X M Y ⋙ associate X M Y = 𝟭 (Right X M Y) := by
  fapply extGenerators
  · intro z; rfl
  · intro b x x' p p' f g
    apply pad
    dsimp only [Functor.comp_map]
    rw [unassociate_native]
    exact restore_right_native X M Y f g
  · intro a b u x p
    apply pad
    dsimp only [Functor.comp_map]
    rw [Reverse.unassociate_outer_balance]
    exact restore_right_balance X M Y u x p

/-- Associativity for two middle categories and one weak curried middle module. Both composites recover every quotient morphism. -/
def associator : Left X M Y ≌ Right X M Y :=
  CategoryTheory.Equivalence.mk (associate X M Y) (Reverse.unassociate X M Y) (eqToIso (roundtrip_left X M Y).symm) (eqToIso (roundtrip_right X M Y))

end ContextualComposition.RelativeTensor.Iterated
