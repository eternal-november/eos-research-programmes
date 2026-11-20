module
public import ContextualComposition.AmbientNativeLetterFrame
public import ContextualComposition.AmbientFoldFrames
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFramedCells
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadCellWhisker ContextadCellPasting ContextadHorizontalLaws AmbientHorizontalRead ContextadWeakAction ContextadAmbientPayload AmbientHorizontalDiagrams
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
open AmbientLetterRead
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
variable (X : Obj.{u,v} B) {i j : Nat} {a b a' b' : obj S i X ⟶ obj S j X} {r s : Map S i j} (c : Cell r s)
def Trace (t : a ⟶ b) : Prop := Reads (S := S) (X := X) (j := i) (k := j) (r := r) (s := s) t c
theorem close (t : a ⟶ b) (n : a' ⟶ b') (e : a = a') (w : b' = b) (eq : t = eqToHom e ≫ n ≫ eqToHom w)
    (h : Trace X c n) : Trace X c t := by
  subst t
  exact AmbientLetterRead.frame (S := S) (X := X) (j := i) (k := j) e w h
end ContextualComposition.GrothendieckStep.AmbientFramedCells
