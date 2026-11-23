module
public import ContextualComposition.RelativeTensorCrossingPayload
public import ContextualComposition.RelativeTensorWhiskeredEquivalence

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u vM uM vN uN vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

/-- Change from two separately paired tensors to the bracketing that exposes the middle two modules. -/
noncomputable def exposeMiddle : opposedPairs X M N Y ≌ innerLeft X M N Y :=
  (associator (leftInner X M) N Y).symm.trans (firstPentagonEquivalence X M N Y)

variable (s : middleComposite N M ⟶ middleComposite M N)

/-- Apply the supplied crossing to the middle pair of the fourfold tensor. -/
noncomputable def crossMiddle : opposedPairs X N M Y ⥤ opposedPairs X M N Y :=
  (exposeMiddle X N M Y).functor ⋙ mapFirst (G := Y) (liftCrossing X M N s) ⋙ (exposeMiddle X M N Y).inverse

/-- The exposed crossing retains arbitrary morphisms of the inner quotient, simultaneously with both outer payload arrows. -/
theorem exposedCrossing_native {i j : B} {x x' : X.obj ⟨i⟩} {y y' : Y.obj ⟨op j⟩}
    {z z' : (column (middleComposite N M) j).obj ⟨op i⟩} (f : x ⟶ x') (h : z ⟶ z') (g : y ⟶ y') :
    (mapFirst (G := Y) (liftCrossing X M N s)).map
      ((Reverse.insertL X (middleComposite N M) Y j).map (productMap ((insertion X (column (middleComposite N M) j) i).map (productMap f h)) g)) =
      (Reverse.insertL X (middleComposite M N) Y j).map
        (productMap ((insertion X (column (middleComposite M N) j) i).map (productMap f (((s.app ⟨j⟩).app ⟨op i⟩).toFunctor.map h))) g) := by
  rw [First.on_native]
  exact congrArg (fun k => (Reverse.insertL X (middleComposite M N) Y j).map (productMap k g))
    (Second.on_native (F := X) (i := i) (s.app ⟨j⟩) f h)

section Multiply
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{max u v vM uM vX uX,max u uM uX})
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN vY uY,max u uN uY})

/-- The endpoint multiplication first crosses NM to MN and then applies the given two one-sided contractions. -/
noncomputable def multiplyAt (m : leftInner X M ⟶ X) (n : rightInner N Y ⟶ Y) :
    opposedPairs X N M Y ⥤ Tensor X Y :=
  crossMiddle X M N Y s ⋙ mapBoth m n

end Multiply
end ContextualComposition.RelativeTensor.Iterated
