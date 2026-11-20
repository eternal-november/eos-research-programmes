module
public import ContextualComposition.AmbientSuffixMateRead
public import ContextualComposition.AmbientFlatInside
public import ContextualComposition.AmbientBoundaryReduction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixView
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates ContextadRoutes
open ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadLawTransport ContextadOuterCharts
open SpanApex AmbientBlockCells AmbientModificationAction AmbientHorizontalFrames ContextadWeakWeight AmbientInsideMateRead
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 550000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} {X Y : Obj.{u,v} B}
open AmbientSuffixRoutes AmbientBoundaryReduction
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell stage
structure Chart (Z : Obj.{u,v} B) (n : Nat) where
  F : Total (underlying Z) (append P S (power S n)).dest ⥤ Total (underlying (obj S n (obj S 1 Z))) (𝟭 B)
  iso : F.IsIso
  commute : stage (S := S) (underlying Z) (power S n) ⋙ chart S (obj S 1 Z) n = F
noncomputable def v0 (Z : Obj.{u,v} B) : Chart (S := S) Z 0 := ⟨chart S Z 1,BlockEvaluation.globalIso S (underlying Z) 1,resolve0 (S := S) Z⟩
noncomputable def v1 (Z : Obj.{u,v} B) : Chart (S := S) Z 1 := ⟨chart S Z 2,BlockEvaluation.globalIso S (underlying Z) 2,resolve1 (S := S) Z⟩
noncomputable def v2 (Z : Obj.{u,v} B) : Chart (S := S) Z 2 := ⟨chart S Z 3,BlockEvaluation.globalIso S (underlying Z) 3,resolve2 (S := S) Z⟩
variable (f : X ⟶ Y) {i j : Nat} (r : Map S i j)
variable {a b : obj S i (obj S 1 X) ⟶ obj S j (obj S 1 Y)} (t : a ⟶ b)
variable (I : Chart (S := S) X i) (J : Chart (S := S) Y j)
def Viewed : Prop :=
  letI := J.iso
  ∀ x, Aligned (J.F.strictInv.map ((totalCell t.hom.as).app (I.F.obj x))) ((flat (S := S) f r).app x)
theorem carry (h : ∀ x, Aligned (atRaw (X := obj S 1 X) (Y := obj S 1 Y) (i := i) (j := j) S t x) ((nested (S := S) f r).app x)) :
    Viewed f r t I J := by
  letI := J.iso
  exact AmbientFlatInside.rechart I.F J.F (chart S (obj S 1 X) i) (chart S (obj S 1 Y) j)
    (stage (S := S) (underlying X) _) (stage (S := S) (underlying Y) _) I.commute J.commute
    (totalCell t.hom.as) (flat (S := S) f r) fun x => (h _).trans (AmbientSuffixMateRead.read f r x).symm
end ContextualComposition.GrothendieckStep.AmbientSuffixView
