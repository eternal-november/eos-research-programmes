module
public import ContextualComposition.RelativeTensorFourFactors

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
set_option backward.isDefEq.respectTransparency false

/-- Reassociation carries a simultaneous native triple of arrows to the same three arrows in the other bracketing. -/
theorem associate_triple_native (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
    {b : B} {c : C} {x x' : X.obj ⟨b⟩} {k k' : (column M c).obj ⟨op b⟩} {y y' : Y.obj ⟨op c⟩}
    (f : x ⟶ x') (g : k ⟶ k') (h : y ⟶ y') :
    (associate X M Y).map ((Reverse.insertL X M Y c).map (productMap ((insertion X (column M c) b).map (productMap f g)) h)) =
      (insertR X M Y b).map (productMap f ((insertM M Y b c).map (productMap g h))) := by
  rw [associate_native,outer_pair,inner_native]
  change (insertR X M Y b).map (productMap (𝟙 x) ((insertM M Y b c).map (productMap (𝟙 k) h))) ≫
    (insertR X M Y b).map (productMap f ((insertM M Y b c).map (productMap g (𝟙 y')))) = _
  rw [← Functor.map_comp]
  apply congrArg (insertR X M Y b).map
  apply Prod.ext
  · exact Category.id_comp _
  · change (insertM M Y b c).map (productMap (𝟙 k) h) ≫ (insertM M Y b c).map (productMap g (𝟙 y')) = _
    rw [← Functor.map_comp]
    exact congrArg (insertM M Y b c).map (Prod.ext (Category.id_comp _) (Category.comp_id _))

variable {D : Type uD} [Category.{vD} D]
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})
variable {b : B} {c : C} {d : D} {x x' : X.obj ⟨b⟩} {m m' : (column M c).obj ⟨op b⟩}
variable {n n' : (column N d).obj ⟨op c⟩} {y y' : Y.obj ⟨op d⟩}
variable (f : x ⟶ x') (g : m ⟶ m') (h : n ⟶ n') (i : y ⟶ y')

abbrev leftFourNative := (Reverse.insertL (leftInner X M) N Y d).map
  (productMap ((insertion (leftInner X M) (column N d) c).map
    (productMap ((insertion X (column M c) b).map (productMap f g)) h)) i)

abbrev rightFourNative := (insertR X M (rightInner N Y) b).map
  (productMap f ((insertM M (rightInner N Y) b c).map (productMap g ((insertM N Y c d).map (productMap h i)))))

theorem twoStep_native :
    (twoStep X M N Y).functor.map (leftFourNative X M N Y f g h i) = rightFourNative X M N Y f g h i := by
  change (associate X M (rightInner N Y)).map ((associate (leftInner X M) N Y).map (leftFourNative X M N Y f g h i)) = rightFourNative X M N Y f g h i
  unfold leftFourNative rightFourNative
  rw [associate_triple_native (leftInner X M) N Y,associate_triple_native X M (rightInner N Y)]

end ContextualComposition.RelativeTensor.Iterated
