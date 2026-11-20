module
public import ContextualComposition.StrictTelRecovery
public import ContextualComposition.StrictTelCartesian
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelAlgebra
open CategoryTheory SpanApex NativeBlocks NativeCleavage
open NativeBlocks.Nested (Over whole)
open StrictSpanAlgebra StrictTelOperations StrictTelNested StrictTelRecovery StrictTelCartesian
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
variable {B : Type b} [Category.{max b w} B] {P : Endpoints.{b,max b w,b,max b w} B} (S : P.Split)

/-- Strict algebra on the actual native telescope. The action has strict
feet and is cartesian; the normally cloven primitive carrier is retained
literally. There is no requirement that an action preserve chosen lifts. -/
structure Algebra where
  action : Over (whole S) (power S 1)
  equations : Equations S action
  cart : CartesianMap action
  cleavage : Cleavage (power S 1).source
  normal : Normal (power S 1).source cleavage

noncomputable def read (A : Algebra S) : Contextad (power S 1) where
  operations := readOperations S A.action
  laws := recoveredLaws S A.action A.equations
  cleavage := A.cleavage
  normal := A.normal
  unitCart := restrictedUnitCart S A.cart
  tensorCart := restrictedTensorCart S A.cart

def write (M : Contextad (power S 1)) : Algebra S where
  action := StrictTelFold.eval S M.operations
  equations := foldEquations S M.operations M.laws
  cart := evalCart S M.operations M.unitCart M.tensorCart
  cleavage := M.cleavage
  normal := M.normal

theorem opsExt {U : Span (B := B)} {M N : Ops U} (u : M.unit = N.unit) (m : M.tensor = N.tensor) :
    M = N := by cases M; cases N; cases u; cases m; rfl

theorem contextadExt {M N : Contextad (power S 1)}
    (o : M.operations = N.operations) (c : M.cleavage = N.cleavage) : M = N := by
  cases M; cases N; cases o; cases c; rfl

theorem algebraExt {M N : Algebra S}
    (o : M.action = N.action) (c : M.cleavage = N.cleavage) : M = N := by
  cases M; cases N; cases o; cases c; rfl

theorem readWrite (M : Contextad (power S 1)) : read S (write S M) = M :=
  contextadExt S (opsExt (restriction_unit S M.operations) (restriction_tensor S M.operations M.laws)) rfl

theorem writeRead (A : Algebra S) : write S (read S A) = A :=
  algebraExt S (unique S A.action _ (read S A).laws A.equations.singleton (readTensor S A.action A.equations)).symm rfl

noncomputable def equivalence : Algebra S ≃ Contextad (power S 1) :=
  ⟨read S,write S,writeRead S,readWrite S⟩

end ContextualComposition.GrothendieckStep.StrictTelAlgebra
