module
public import ContextualComposition.AmbientLetterRead
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientNativeLetterFrame
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
variable (X : Obj.{u,v} B) {i j : Nat} {r s : Map S i j} (c : Cell r s) (p : gradeCart r) (q : gradeCart s)
variable {u v : obj S i X ⟶ obj S j X} (e : u = oper S r p X) (w : v = oper S s q X) (l : u ≅ v)
def Native : Prop := Reads (X := X) (j := i) (k := j) (u := u) (v := v) (r := r) (s := s) l.hom c
theorem trace (h : (eqToIso e ≪≫ AmbientNativeModification.cmp c p q X ≪≫ eqToIso w.symm) = l) : Native X c l := by
  subst l
  exact frameIso (S := S) (X := X) e w.symm (AmbientNativeModification.cmp c p q X) (AmbientHorizontalRead.cmp (X := X) c p q)
end ContextualComposition.GrothendieckStep.AmbientNativeLetterFrame
