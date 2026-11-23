module
public import ContextualComposition.RelativeTensorUnassociate

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

theorem associate_native {c : C} {p p' : Tensor X (column M c)} {y y' : Y.obj ⟨op c⟩} (f : p ⟶ p') (g : y ⟶ y') :
    (associate X M Y).map ((Reverse.insertL X M Y c).map (productMap f g)) = (outerFiber X M Y c).map (productMap f g) :=
  (associatingCocone X M Y).extend_generator (Edge.native (F := leftInner X M) (G := Y) (i := c) f g)

theorem unassociate_native {b : B} {x x' : X.obj ⟨b⟩} {q q' : Tensor (row M b) Y} (f : x ⟶ x') (g : q ⟶ q') :
    (Reverse.unassociate X M Y).map ((insertR X M Y b).map (productMap f g)) = (Reverse.outerFiber X M Y b).map (productMap f g) :=
  (Reverse.outerCocone X M Y).extend_generator (Edge.native (F := X) (G := rightInner M Y) (i := b) f g)

private theorem pad {D : Type*} [Category* D] {a b : D} {f g : a ⟶ b} (h : f = g) : f ≫ 𝟙 _ = 𝟙 _ ≫ g := by simpa using h

theorem left_inner_recover {c : C} (y : Y.obj ⟨op c⟩) : (innerCocone X M Y c y).extend ⋙ Reverse.unassociate X M Y = Reverse.keep X M Y y := by
  fapply extGenerators
  · intro z; rfl
  · intro b x x' m m' p q
    apply pad
    dsimp only [Functor.comp_map]
    rw [inner_native, unassociate_native, Reverse.outer_step]
    rfl
  · intro a b u x m
    apply pad
    dsimp only [Functor.comp_map]
    rw [inner_balance,Reverse.unassociate_outer_balance]
    rfl

theorem right_inner_recover {b : B} (x : X.obj ⟨b⟩) : (Reverse.innerCocone X M Y x).extend ⋙ associate X M Y = keep X M Y x := by
  fapply extGenerators
  · intro z; rfl
  · intro c m m' y y' p q
    apply pad
    dsimp only [Functor.comp_map]
    rw [Reverse.inner_native,associate_native,outer_step]
    rfl
  · intro c d v m y
    apply pad
    dsimp only [Functor.comp_map]
    rw [Reverse.inner_balance,associate_outer_balance]
    rfl

theorem outer_only_inner {c : C} {z z' : Tensor X (column M c)} (y : Y.obj ⟨op c⟩) (f : z ⟶ z') :
    (outerFiber X M Y c).map (productMap f (𝟙 y)) = (innerCocone X M Y c y).extend.map f := by
  let H := innerFamily X M Y c ⋙ extendFunctor
  change (H.map (𝟙 y)).app z ≫ _ = _
  rw [H.map_id,NatTrans.id_app]; exact Category.id_comp _

theorem reverse_only_inner {b : B} (x : X.obj ⟨b⟩) {z z' : Tensor (row M b) Y} (f : z ⟶ z') :
    (Reverse.outerFiber X M Y b).map (productMap (𝟙 x) f) = (Reverse.innerCocone X M Y x).extend.map f := by
  let H := Reverse.innerFamily X M Y b ⋙ extendFunctor
  change (H.map (𝟙 x)).app z ≫ _ = _
  rw [H.map_id,NatTrans.id_app]; exact Category.id_comp _

theorem unassociate_leaf {c : C} (z : Tensor X (column M c)) {y y' : Y.obj ⟨op c⟩} (g : y ⟶ y') :
    (Reverse.unassociate X M Y).map (leafMap X M Y z g) = (Reverse.insertL X M Y c).map (productMap (𝟙 z) g) := by
  obtain ⟨⟨b,x,m⟩⟩ := z
  unfold leafMap
  rw [unassociate_native,reverse_only_inner,Reverse.inner_native]
  change (Reverse.insertL X M Y c).map (productMap ((insertion X (column M c) b).map (𝟙 (x,m))) g) = _
  rw [Functor.map_id]
  rfl

theorem associate_leaf {b : B} (z : Tensor (row M b) Y) {x x' : X.obj ⟨b⟩} (f : x ⟶ x') :
    (associate X M Y).map (Reverse.leafMap X M Y z f) = (insertR X M Y b).map (productMap f (𝟙 z)) := by
  obtain ⟨⟨c,m,y⟩⟩ := z
  unfold Reverse.leafMap
  rw [associate_native,outer_only_inner,inner_native]
  change (insertR X M Y b).map (productMap f ((insertion (row M b) Y c).map (𝟙 (m,y)))) = _
  rw [Functor.map_id]
  rfl

end ContextualComposition.RelativeTensor.Iterated
