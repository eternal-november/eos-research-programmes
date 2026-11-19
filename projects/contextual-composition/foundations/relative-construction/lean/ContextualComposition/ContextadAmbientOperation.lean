module
public import ContextualComposition.ContextadAmbientUnary
public import ContextualComposition.ContextadWeakWeight
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadAmbientPayload
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue NativeCleavage
open ContextadWeakAction ContextadModification BoundaryPaste SpanApex TelescopeSquares NativeBlocks ContextadRoutes ContextadLawTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {Y Z : PackedCuts.Psh.{u,max u v,u,v} B} (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor')
noncomputable def blockTotal (n : Nat) := (BlockEvaluation.global S Y n).strictInv ⋙ atEndpoint a (power S n).dest ⋙ BlockEvaluation.global S Z n
theorem blockOver (n : Nat) : blockTotal S a n ⋙ proj (PackedFree.pow S Z n) = proj (PackedFree.pow S Y n) := by
  unfold blockTotal; simp only [Functor.assoc]
  rw [show BlockEvaluation.global S Z n ⋙ proj (PackedFree.pow S Z n) = _ from BlockEvaluation.globalOver S Z n]
  rw [← Functor.assoc (atEndpoint a (power S n).dest),show atEndpoint a (power S n).dest ⋙ gradeProjection = _ from actionGrade _ (totalStrong a) (strongOver a)]
  exact invOver _ _ _ (BlockEvaluation.globalOver S Y n)
theorem blockPres (n : Nat) : Pres (blockTotal S a n) (proj (PackedFree.pow S Y n)) (proj (PackedFree.pow S Z n)) := by
  intro x y f h
  apply (BlockCartesian.cartesian_iff (BlockEvaluation.global S Z n) (BlockCartesian.isoIncoming _) _ _).mp
  rw [BlockEvaluation.globalOver]
  apply liftCart a (power S n).dest (power S n).source (nativeChoice (S := S) n)
  apply (BlockCartesian.cartesian_iff (BlockEvaluation.global S Y n).strictInv (BlockCartesian.isoIncoming _) _ _).mp
  rwa [invOver _ _ _ (BlockEvaluation.globalOver S Y n)]
variable {S} {i j : Nat} (r : Map S i j)
noncomputable abbrev left := global Y r ⋙ blockTotal S a j
noncomputable abbrev right := blockTotal S a i ⋙ global Z r
noncomputable abbrev rawIso := ContextadWeakWeight.weakSquare (power S i).dest (power S j).dest r.grade r.leg a
noncomputable abbrev coreIso := isoWhiskerLeft (BlockEvaluation.global S Y i).strictInv (isoWhiskerRight (rawIso a r) (BlockEvaluation.global S Z j))
theorem toLeft : left a r = (BlockEvaluation.global S Y i).strictInv ⋙ ContextadWeakWeight.lRoute (power S i).dest (power S j).dest r.grade r.leg a ⋙ BlockEvaluation.global S Z j :=
  BlockEvaluation.cancelMiddle _ (raw Y r) (BlockEvaluation.global S Y j) (BlockEvaluation.global S Y j).strictInv
    (atEndpoint a (power S j).dest) _ _ (BlockEvaluation.global S Y j).asIsomorphism.unit_eq.symm rfl
theorem toRight : right a r = (BlockEvaluation.global S Y i).strictInv ⋙ ContextadWeakWeight.rRoute (power S i).dest (power S j).dest r.grade r.leg a ⋙ BlockEvaluation.global S Z j :=
  BlockEvaluation.cancelMiddle _ (atEndpoint a (power S i).dest) (BlockEvaluation.global S Z i) (BlockEvaluation.global S Z i).strictInv
    (raw Z r) _ _ (BlockEvaluation.global S Z i).asIsomorphism.unit_eq.symm rfl
noncomputable def operationSquare : left a r ≅ right a r := eqToIso (toLeft a r) ≪≫ coreIso a r ≪≫ eqToIso (toRight a r).symm
theorem operationBase (x) : Pure ((proj (PackedFree.pow S Z j)).map ((operationSquare a r).hom.app x)) := by
  apply castPure
  intro z
  let k := (rawIso a r).hom.app ((BlockEvaluation.global S Y i).strictInv.obj z)
  change Pure (((BlockEvaluation.global S Z j ⋙ proj (PackedFree.pow S Z j)).map k))
  rw [show BlockEvaluation.global S Z j ⋙ proj (PackedFree.pow S Z j) = _ from BlockEvaluation.globalOver S Z j]
  exact pureMap (power S j).source (ContextadWeakWeight.weakGrade _ _ r.grade r.leg a _)
theorem leftOver : left a r ⋙ proj (PackedFree.pow S Z j) = proj (PackedFree.pow S Y i) :=
  (congrArg (global Y r ⋙ ·) (blockOver S a j)).trans (over Y r)
theorem rightOver : right a r ⋙ proj (PackedFree.pow S Z j) = proj (PackedFree.pow S Y i) :=
  (congrArg (blockTotal S a i ⋙ ·) (over Z r)).trans (blockOver S a i)
noncomputable def operationMod (h : gradeCart r) :=
  modification _ _ (left a r) (right a r) (leftOver a r) (rightOver a r) (operationSquare a r) (operationBase a r)
    (fun f p => blockPres S a j _ (globalPres Y r h f p)) (fun f p => globalPres Z r h _ (blockPres S a i f p))
end ContextualComposition.GrothendieckStep.ContextadAmbientPayload
