module
public import ContextualComposition.AmbientWeightCoordinates
public import ContextualComposition.AmbientFoldReading
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientWeightPicture
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open NativeBlocks ContextadRoutes ContextadLawTransport ContextadModification ContextadNativeLaws ContextadOuterCharts
open AmbientCoordinates AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality AmbientFoldReading AmbientFlatWeight
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
open AmbientWeightLetters AmbientModificationAction
section Generic
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
variable (I : A ⥤ C) (J : B ⥤ D) [J.IsIso] {F G : C ⥤ D} {R W : A ⥤ B}
def Picture (n : F ⟶ G) (q : R ⟶ W) : Prop := ∀ x, Aligned (J.strictInv.map (n.app (I.obj x))) (q.app x)
end Generic
variable {k i j : Nat} (r : Map S i j) (p : gradeCart r)
variable (I : View (S := S) X k i) (J : View (S := S) Y k j)
def Evidence : Prop :=
  letI := J.iso
  Picture I.F J.F (totalCell (cell S k (comparison S r p f).inv).hom.as) (AmbientComparisonRead.q S (inside k r) f)
theorem collect : Evidence f r p I J := AmbientFlatWeight.reading f r p I J
end ContextualComposition.GrothendieckStep.AmbientWeightPicture
