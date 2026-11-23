module
public import ContextualComposition.RelativeTensorMixedMultiplication
public import ContextualComposition.RelativeTensorModuleRows
public import ContextualComposition.RelativeTensorMiddleRow
public import ContextualComposition.RelativeTensorOuterRow
public import ContextualComposition.RelativeTensorUnitModule
public import ContextualComposition.RelativeTensorRightContraction

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]

section Unit
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{v,v}))
variable (jM : unitModule B ⟶ M) (jN : unitModule B ⟶ N)

/-- The endpoint mixed unit splits the represented pure arrow using the inverse right unitor and applies the two supplied units. -/
def mixedUnitAt (a b : B) : Discrete (a ⟶ b) ⥤ (column (middleComposite M N) b).obj ⟨op a⟩ :=
  RightUnit.sectionFunctor b (row (unitModule B) a) ⋙ mapBoth (rowMap jM a) (jN.app ⟨b⟩)

theorem mixedUnitAt_obj {a b : B} (p : a ⟶ b) :
    (mixedUnitAt M N jM jN a b).obj (Discrete.mk p) =
      (insertion (row M a) (column N b) b).obj
        (((jM.app ⟨b⟩).app ⟨op a⟩).toFunctor.obj (Discrete.mk p), ((jN.app ⟨b⟩).app ⟨op b⟩).toFunctor.obj (Discrete.mk (𝟙 b))) := rfl
end Unit

section Multiplication
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))

/-- Restrict the supplied global one-sided multiplication to the covariant row presentation of its source. -/
def rowMultiplication (m : middleComposite M M ⟶ M) (a : B) : leftInner (row M a) M ⟶ row M a :=
  Eq.mp (congrArg (fun F => F ⟶ row M a) (middleRow M M a)) (rowMap m a)

/-- The multiplication component on the genuine source and target fibres of MN, using the supplied crossing and original one-sided multiplications. -/
noncomputable def mixedMultiplicationAt (s : middleComposite N M ⟶ middleComposite M N)
    (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N) (a b : B) :
    (column (middleComposite (middleComposite M N) (middleComposite M N)) b).obj ⟨op a⟩ ⥤
      (column (middleComposite M N) b).obj ⟨op a⟩ :=
  (identifyFirst (middleRow M N a) (column (middleComposite M N) b)).functor ⋙
    crossMiddle (row M a) M N (column N b) s ⋙
    mapBoth (rowMultiplication.{v,u,vM,uM} M m a) (n.app ⟨b⟩)

end Multiplication
end ContextualComposition.RelativeTensor.Iterated
