module
public import ContextualComposition.RelativeTensorWhiskeredEquivalence
public import ContextualComposition.RelativeTensorFourGeneratorComparison
public import ContextualComposition.RelativeTensorOuterRowIdentity

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))

theorem associate_inner_balance (Z : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
    {b b' : B} {c : C} (u : b ⟶ b') (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b'⟩) (y : Z.obj ⟨op c⟩) :
    (associate X M Z).map ((Reverse.insertL X M Z c).map (productMap (balancing X (column M c) u x m).hom (𝟙 y))) =
      (balancing X (rightInner M Z) u x ((insertM M Z b' c).obj (m,y))).hom := by
  rw [associate_native,outer_only_inner,inner_balance]

variable {D : Type uD} [Category.{vD} D]
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

section Native
variable {b : B} {c : C} {d : D} {x x' : X.obj ⟨b⟩} {m m' : (column M c).obj ⟨op b⟩}
variable {n n' : (column N d).obj ⟨op c⟩} {y y' : Y.obj ⟨op d⟩}
variable (f : x ⟶ x') (g : m ⟶ m') (h : n ⟶ n') (i : y ⟶ y')

abbrev innerRightNative := (insertR X (middleComposite M N) Y b).map
  (productMap f ((insertM (middleComposite M N) Y b d).map (productMap ((insertion (row M b) (column N d) c).map (productMap g h)) i)))

theorem firstTwo_native : (firstTwoEdges X M N Y).functor.map (leftFourNative X M N Y f g h i) =
    innerRightNative X M N Y f g h i := by
  change (associate X (middleComposite M N) Y).map ((mapFirst (G := Y) (outerAssociator X M N)).map (leftFourNative X M N Y f g h i)) = _
  unfold leftFourNative
  rw [First.on_native]
  change (associate X (middleComposite M N) Y).map ((Reverse.insertL X (middleComposite M N) Y d).map
    (productMap ((associate X M (column N d)).map _) i)) = _
  rw [associate_triple_native X M (column N d)]
  exact associate_triple_native X (middleComposite M N) Y f _ i

theorem lastRow_native : (OuterRow.direct M N Y ⟨op b⟩).map
    ((insertM (middleComposite M N) Y b d).map (productMap ((insertion (row M b) (column N d) c).map (productMap g h)) i)) =
    (insertM M (rightInner N Y) b c).map (productMap g ((insertM N Y c d).map (productMap h i))) := by
  dsimp only [OuterRow.direct,Functor.comp_map]
  erw [First.on_native (OuterRow.rowId M N ⟨op b⟩)]
  exact associate_triple_native (row M b) N Y g h i

end Native
section Middle
variable {b : B} {c c' : C} {d : D} (v : c ⟶ c') (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b⟩)
variable (n : (column N d).obj ⟨op c'⟩) (y : Y.obj ⟨op d⟩)

abbrev finalMiddleBalance := (insertR X M (rightInner N Y) b).map (productMap (𝟙 x)
  (balancing (row M b) (rightInner N Y) v m ((insertM N Y c' d).obj (n,y))).hom)

abbrev innerRightMiddleBalance := (insertR X (middleComposite M N) Y b).map (productMap (𝟙 x)
  ((insertM (middleComposite M N) Y b d).map (productMap (balancing (row M b) (column N d) v m n).hom (𝟙 y))))

theorem twoStep_middle : (twoStep X M N Y).functor.map
    (farLeftBalanceC X M N Y v ((insertion X (column M c) b).obj (x,m)) n y) = finalMiddleBalance X M N Y v x m n y := by
  let z := (insertion X (column M c) b).obj (x,m)
  change (associate X M (rightInner N Y)).map ((associate (leftInner X M) N Y).map
    ((Reverse.insertL (leftInner X M) N Y d).map (productMap (balancing (leftInner X M) (column N d) v z n).hom (𝟙 y)))) = _
  rw [associate_inner_balance,associate_outer_balance]
  rfl

theorem firstTwo_middle : (firstTwoEdges X M N Y).functor.map
    (farLeftBalanceC X M N Y v ((insertion X (column M c) b).obj (x,m)) n y) = innerRightMiddleBalance X M N Y v x m n y := by
  let z := (insertion X (column M c) b).obj (x,m)
  change (associate X (middleComposite M N) Y).map ((mapFirst (G := Y) (outerAssociator X M N)).map
    ((Reverse.insertL (leftInner X M) N Y d).map (productMap (balancing (leftInner X M) (column N d) v z n).hom (𝟙 y)))) = _
  rw [First.on_native]
  change (associate X (middleComposite M N) Y).map ((Reverse.insertL X (middleComposite M N) Y d).map
    (productMap ((associate X M (column N d)).map (balancing (leftInner X M) (column N d) v z n).hom) (𝟙 y))) = _
  rw [associate_outer_balance]
  exact associate_triple_native X (middleComposite M N) Y (𝟙 x) (balancing (row M b) (column N d) v m n).hom (𝟙 y)

theorem lastRow_middle : (OuterRow.direct M N Y ⟨op b⟩).map
    ((insertM (middleComposite M N) Y b d).map (productMap (balancing (row M b) (column N d) v m n).hom (𝟙 y))) =
    (balancing (row M b) (rightInner N Y) v m ((insertM N Y c' d).obj (n,y))).hom := by
  dsimp only [OuterRow.direct,Functor.comp_map]
  erw [First.on_native (OuterRow.rowId M N ⟨op b⟩)]
  exact associate_inner_balance (row M b) N Y v m n y

end Middle
end ContextualComposition.RelativeTensor.Iterated
