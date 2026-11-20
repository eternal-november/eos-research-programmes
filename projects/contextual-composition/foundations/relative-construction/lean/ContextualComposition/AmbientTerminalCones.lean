module
public import ContextualComposition.AmbientTerminalViews
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientTerminalCones
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadOuterRigidity ContextadDisjointCut AmbientChosenTail
open ContextadModification
open AmbientBicategory AmbientCoordinates ContextadWeakWeight ContextadWeakAction ContextadCellWhisker
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
attribute [local irreducible] BlockEvaluation.global NativeBlocks.blocks
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
variable (f g : Map S 2 1)
set_option linter.defProp false in
def rightSrc (x : Total Y (power S 4).dest) :=
  congrArg (finalOne (S := S) Y).obj (Functor.congr_obj (rawCompose Y (inside 2 g) (suffix f)) x)
noncomputable def right (x : Total Y (power S 4).dest) :=
  eqToHom (rightSrc Y f g x) ≫ rTail Y f g x
theorem rightRead (x : Total Y (power S 4).dest) : Aligned (right Y f g x) (rTail Y f g x) := by
  exact ⟨rightSrc Y f g x,rfl,by simp [right]⟩
theorem rightGrade (x : Total Y (power S 4).dest) :
    Aligned (gradeMap (right Y f g x)) ((ContextadDisjointCut.rightCone f g).app (grade Y _ x)) :=
  ((rightRead Y f g x).map gradeProjection).trans (rightTip f g _).symm
theorem leftGrade (x : Total Y (power S 4).dest) :
    Aligned (gradeMap (lTail Y f g x)) ((ContextadDisjointCut.leftCone f g).app (grade Y _ x)) :=
  (leftTip f g _).symm
theorem restrictionPure {i j : Nat} (r : Map S i j) {a b : Total Y (power S i).dest} (w : a ⟶ b)
    (h : Pure (payloadMap w)) : Pure (payloadMap ((raw Y r).map w)) := by
  rw [show payloadMap ((raw Y r).map w) = _ from restrict_payload Y _ _ r.grade r.leg w]
  exact pureComp (pureMap _ h) ⟨_,rfl⟩
set_option maxHeartbeats 1800000 in
theorem rawFactor (p : gradeCart g) (x : Total Y (power S 4).dest) :
    Aligned ((finalOne (S := S) Y).map ((rawCell Y (disjoint f g p)).hom.app x) ≫ right Y f g x) (lTail Y f g x) := by
  let t := grade Y _ x
  let c := (rawCell Y (disjoint f g p)).hom.app x
  have gr : Aligned (gradeMap ((finalOne (S := S) Y).map c)) ((exchange f g p).hom.app t) := by
    change Aligned ((NativeAssoc.last S 1).map (gradeMap c)) _
    rw [show gradeMap c = _ from readGrade (disjoint f g p) Y x]
    exact NativeCube.ofEq (assembledTip f g p t)
  apply ContextadChosenCone.alignChosen Y (power S 1).dest (Functor.congr_obj (innerTail Y g) x)
  · exact (gr.comp (rightGrade Y f g x)).trans ((NativeCube.ofEq (exchangeFac f g p t)).trans (leftGrade Y f g x).symm)
  · apply WeightedCells.totalPureComp
    · exact readPure (disjoint f g p) Y x
    · exact payloadAligned (rightRead Y f g x) (pureId _)
  · exact restrictionPure Y g ((wideArrow Y f).app x) (pureId _)
end
end ContextualComposition.GrothendieckStep.AmbientTerminalCones
