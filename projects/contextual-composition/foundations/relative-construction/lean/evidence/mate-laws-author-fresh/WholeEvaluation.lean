import ContextualComposition.MateLaws
open CategoryTheory Opposite ContextualComposition.GrothendieckStep Families
open MateLaws.All
-- The base map Bool → Bool is constant; no invertibility or trivial action is needed.
#check evaluationUnitDiagram splitEndpoints presheaf Bool
#check evaluationCompDiagram splitEndpoints presheaf collapse (selectPoint true)
def zeroPayload : presheaf.obj (op Bool) := fun b => if b then Bool else Empty
noncomputable def wholeAtZero :=
  (CoproductSpan.All.evaluation splitEndpoints presheaf Bool).inverse.obj ⟨0,zeroPayload⟩
#check evaluationComp splitEndpoints presheaf collapse (selectPoint true) wholeAtZero
noncomputable def wholeAtOne :=
  (CoproductSpan.All.evaluation splitEndpoints presheaf Bool).inverse.obj ⟨1,sourcePair⟩
#check evaluationComp splitEndpoints presheaf collapse (selectPoint true) wholeAtOne
