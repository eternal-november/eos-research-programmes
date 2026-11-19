module
public import ContextualComposition.ContextadExchangeData
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadDisjointCut
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadSchedule ContextadLawTransport
open TelescopeSquares NativeAssoc FibreValue NativeTrace NativeCleavage BoundaryPaste ContextadOuterCharts ContextadModification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} (f g : Map S 2 1)
theorem rightInsideLeg (x : (power S 4).apex) : Aligned ((inside 2 g).leg.app x) (lastLeg g x) :=
  (ContextadInsideCells.leg (S := S) (i := 2) (j := 1) 2 g x).trans (ContextadPayloadModification.appChange g.leg (Functor.congr_obj (tail₂ S) x))
theorem rightOutsideLeg (x : (power S 4).apex) : Aligned ((suffix f).leg.app ((inside 2 g).grade.obj x)) ((right P S).map ((rightCone f g).app x)) :=
  (snocLeg (S := S) (i := 2) (j := 1) f ((inside 2 g).grade.obj x)).trans ((rightTip f g x).map (right P S)).symm
set_option maxHeartbeats 1300000 in
theorem rightLegAt (x : (power S 4).apex) : Aligned ((rhs f g).leg.app x) ((right P S).map ((rightCone f g).app x) ≫ lastLeg g x) := by
  dsimp only [rhs,ContextadRoutes.comp,pasteLift,NatTrans.comp_app,whiskerLeft_app]
  exact (rightOutsideLeg f g x).comp (rightInsideLeg g x)
noncomputable def disjoint (p : gradeCart g) : Cell (lhs f g) (rhs f g) where
  grade := assembled f g p
  source x := pureMap (left P) (assembledHead f g p x)
  endpoint := by
    apply NatTrans.ext; funext x
    have e := congrArg (right P S).map (assembledTip f g p x)
    have h := congrArg (right P S).map (exchangeFac f g p x)
    rw [(right P S).map_comp] at h
    apply Aligned.eq
    apply ((NativeCube.ofEq e).comp (rightLegAt f g x)).trans
    exact (NativeCube.ofEq ((Category.assoc ..).symm.trans (congrArg (· ≫ lastLeg g x) h))).trans (leftLegAt f g x).symm
end ContextualComposition.GrothendieckStep.ContextadDisjointCut
