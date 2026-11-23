module
public import ContextualComposition.PayloadLaws
public import ContextualComposition.PointwisePseudonaturalEquivalence

@[expose] public section
namespace ContextualComposition.GrothendieckStep.PayloadLaws.All
open CategoryTheory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe b w
variable {B : Type b} [Category.{w} B] {Q : Endpoints.{b,w,b,w} B} (R : Q.Split) (A : B)

/-- The single-span comparison is an indexed adjoint equivalence over ordinary payload maps at a fixed base object. -/
noncomputable def fixedBasePayloadEquivalence :
    Bicategory.Equivalence (wholeAction R A).toPseudofunctor' (iterateAction R A).toPseudofunctor' := by
  letI : ∀ Y, ((strong R A).app Y).toFunctor.IsEquivalence := fun Y => strongComponent R A Y.as
  exact PseudonaturalInverse.equivalence (strong R A)

theorem fixedBasePayloadEquivalence_hom : (fixedBasePayloadEquivalence R A).hom = strong R A := rfl

end ContextualComposition.GrothendieckStep.PayloadLaws.All
