module
public import ContextualComposition.AmbientOutsideLetters
public import ContextualComposition.AmbientFourToTwo
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientScheduleFragment
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
open AmbientNativeLetterFrame ContextadAppendCells
variable (X : Obj.{u,v} B) {n : Nat}
def Fragment (e : ContextadHorizontalLaws.Edge (S := S) n) {a b : obj S n X ⟶ obj S 1 X} (t : a ⟶ b) : Prop :=
  Reads (S := S) (X := X) (j := n) (k := 1) (r := e.src) (s := e.dst) t e.cell
section Post
variable {r s : Map S n 2} (c : Cell r s) {a b : obj S n X ⟶ obj S 2 X} (t : a ⟶ b) (m : ContextadTotal.Native S)
theorem post (h : Reads (S := S) (X := X) (j := n) (k := 2) t c) :
    Fragment X (ContextadHorizontalLaws.edge (ContextadCellWhisker.after c (tensor m))) (t ▷ M S X m) :=
  AmbientHorizontalRead.post (S := S) (X := X) (j := n) (k := 2) (l := 1) h (M S X m) (tensor m) (opEncode S (tensor m) m.cart X)
end Post
section Pre
variable {r s : Map S 3 1} (c : Cell r s)
variable {U : Obj.{u,v} B} {a : obj S 3 X ⟶ U} {b : U ⟶ obj S 1 X} {a' : obj S 3 X ⟶ U} {b' : U ⟶ obj S 1 X}
variable (t : a ≫ b ≅ a' ≫ b') (f : obj S n X ⟶ obj S 3 X) (p : Map S n 3)
theorem pre (h : Native (S := S) (i := 3) (j := 1) X c t) (k : encode (X := X) (Y := X) (i := n) (j := 3) S f = raw (underlying X) p) :
    Fragment X (ContextadHorizontalLaws.edge (ContextadCellWhisker.before c p)) (middle f a b t).hom := by
  simp only [middle,Iso.trans_hom,Strict.associator_eqToIso,Iso.symm_hom,eqToIso.hom,eqToIso.inv,whiskerLeftIso_hom]
  exact AmbientLetterRead.frame (S := S) (X := X) (j := n) (k := 1) (Category.assoc f a b) (Category.assoc f a' b').symm (AmbientHorizontalRead.pre (S := S) (X := X) (i := n) (j := 3) (k := 1) h f p k)
end Pre
end ContextualComposition.GrothendieckStep.AmbientScheduleFragment
