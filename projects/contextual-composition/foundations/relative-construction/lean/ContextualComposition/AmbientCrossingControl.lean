module
public import ContextualComposition.AmbientFourToTwo
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientCrossingControl
open CategoryTheory CategoryTheory.Functor TelescopeSquares FibreValue
open NativeBlocks ContextadRoutes AmbientCoordinates AmbientBicategory AmbientExchangeDemand AmbientExchangeChecklist
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1)
variable {a b : obj S 4 X ⟶ obj S 2 X} (t : a ⟶ b)
def Contrast (x : Raw S X 4) : Prop :=
  let v := atRaw (X := X) (Y := X) (i := 4) (j := 2) S t x
  ¬ Pure v
def Payload (x : Raw S X 4) : Prop :=
  Pure (payloadMap (atRaw (X := X) (Y := X) (i := 4) (j := 2) S t x))
def Separated (x : Raw S X 4) : Prop := (encode (X := X) (Y := X) (i := 4) (j := 2) S a).obj x ≠ (encode (X := X) (Y := X) (i := 4) (j := 2) S b).obj x
theorem control (x : Raw S X 4) (d : Separated (a := a) (b := b) X x)
    (h : AmbientFourToTwo.Point X f g t x) : Contrast X t x ∧ Payload X t x :=
  ⟨fun p => d p.choose,h.2⟩
end ContextualComposition.GrothendieckStep.AmbientCrossingControl
