import ContextualComposition.AmbientNestedGrade
/-! Independent supplement on the frozen post-229 ambient coherence tranche.
The final theorem concerns the actual pre-final inverse multiplication square, not
an arbitrary parallel iso. The fixed last-grade factor and final payload are
tests, not proofs that the interchange satisfies either test. -/
open CategoryTheory CategoryTheory.Functor Opposite
open ContextualComposition.GrothendieckStep FibreValue
open AmbientBicategory AmbientCoordinates NativeBlocks AmbientHorizontalDiagrams AmbientHorizontalFrames AmbientExchangeDemand
open AmbientObservationChart AmbientNestedGrade AmbientModificationAction
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace AmbientIndependent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B)
def Head {a b : Raw S X 2} (v : a ⟶ b) : Prop := Pure (gradeMap (gradeMap v))
def Nest {a b : Raw S (obj S 1 X) 1} (v : a ⟶ b) : Prop := Pure (gradeMap v)
variable {a b : obj S 4 X ⟶ obj S 2 X} (t : a ⟶ b)
def inFlat (x : Raw S X 4) : Prop := Head X (atRaw (X := X) (Y := X) (i := 4) (j := 2) S t x)
def inNest (y : Raw S (obj S 2 X) 2) : Prop := Nest X (atRaw (X := obj S 2 X) (Y := obj S 1 X) (i := 2) (j := 1) S t y)
theorem move (h : ∀ y, inNest X t y) (x : Raw S X 4) : inFlat X t x := by
  let n := totalCell t.hom.as
  exact headOfNested X (chart S (obj S 2 X) 2) n h ((chart S X 4).obj x)
end
end AmbientIndependent

open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep
open FibreValue AmbientBicategory AmbientCoordinates NativeBlocks AmbientHorizontalDiagrams AmbientHorizontalFrames
open AmbientObservationChart AmbientNestedGrade AmbientModificationAction
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace AmbientIndependent
noncomputable section
set_option maxHeartbeats 250000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B)
variable {a b : obj S 2 (obj S 2 X) ⟶ obj S 1 (obj S 1 X)}
def nestToFlat (t : a ⟶ b)
    (h : ∀ y : Raw S (obj S 2 X) 2,
      Pure (gradeMap (atRaw (X := obj S 2 X) (Y := obj S 1 X) (i := 2) (j := 1) (f := a) (g := b) S t y))) :
    ∀ x, inFlat (S := S) X (a := a) (b := b) t x := move X t h
end
end AmbientIndependent

open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep
open FibreValue AmbientBicategory AmbientCoordinates NativeBlocks AmbientHorizontalDiagrams AmbientHorizontalFrames
open AmbientObservationChart AmbientNestedGrade AmbientModificationAction
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace AmbientIndependent
noncomputable section
set_option maxHeartbeats 400000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (m : ContextadTotal.Native S)
set_option linter.defProp false in
def flatGate := nestToFlat X (S := S) (squareM S m (M S X m)).inv
  (@nestedGrade B _ P S m (obj S 2 X) (obj S 1 X) (M S X m))
end
end AmbientIndependent

open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep
open NativeBlocks TelescopeSquares FibreValue ContextadRoutes ContextadDisjointCut ContextadLawTransport ContextadModification
open AmbientCoordinates AmbientBicategory AmbientExchangeChecklist AmbientExchangeFactors ContextadCellWhisker
open AmbientHorizontalDiagrams AmbientHorizontalFrames AmbientExchangeDemand
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace AmbientIndependent
noncomputable section
set_option maxHeartbeats 300000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1)
def Remaining (t : (power S 4).apex) {a b : Raw S X 2} (v : a ⟶ b) : Prop :=
 (∃ w : TailArrow f g t, Aligned ((NativeAssoc.last S 1).map (gradeMap v)) w ∧ Factors f g t w) ∧ Pure (payloadMap v)
theorem dropFirst (t : (power S 4).apex) {a b : Raw S X 2} (v : a ⟶ b) (h : Head X v) :
    Row X f g t v ↔ Remaining X f g t v := ⟨fun z => ⟨z.1.2,z.2⟩,fun z=> ⟨⟨h,z.1⟩,z.2⟩⟩
variable {a b : obj S 4 X ⟶ obj S 2 X}
theorem dropAll (t : a ⟶ b) (h : ∀ x, inFlat X t x) {d : Prop}
    (c : d ↔ ∀ x, Row X f g (grade (underlying X) (power S 4).dest x) (atRaw (X := X) (Y := X) (i := 4) (j := 2) S t x)) :
    d ↔ ∀ x, Remaining X f g (grade (underlying X) (power S 4).dest x) (atRaw (X := X) (Y := X) (i := 4) (j := 2) S t x) :=
  c.trans (forall_congr' fun x => dropFirst X f g _ _ (h x))
variable (m : ContextadTotal.Native S)
set_option linter.defProp false in
def twoTests := dropAll X (tensor m) (tensor m) (interchange X m).hom (flatGate X m) (actual X m)
end
end AmbientIndependent
#print axioms AmbientIndependent.flatGate
#print axioms AmbientIndependent.twoTests
#check AmbientIndependent.twoTests
