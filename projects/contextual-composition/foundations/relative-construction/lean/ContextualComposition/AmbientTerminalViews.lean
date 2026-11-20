module
public import ContextualComposition.AmbientChosenTail
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

set_option linter.defProp false in
def tail2Frame :=
  NativePacked.Lift.total_eq Y (e := (power S 4).dest) (d := (power S 2).dest) (H := (blocks S 2 2).rest) (J := leaf₂ S) (h := (blocks S 2 2).dest) (k := (congrArg (· ⋙ (power S 2).dest) (tail₂ S).symm).trans (blocks S 2 2).dest) (tail₂ S)
set_option linter.defProp false in
def tail1Frame :=
  NativePacked.Lift.total_eq Y (e := (power S 3).dest) (d := (right P S)) (H := (blocks S 2 1).rest) (J := NativeAssoc.last S 2) (h := (blocks S 2 1).dest) (k := NativeAssoc.last_dst S 2) (tailOne (S := S) 2)
variable (f g : Map S 2 1)
abbrev inner := raw Y (inside 2 g)
set_option linter.defProp false in
def innerTail :=
  (congrArg (inner Y g ⋙ ·) (tail1Frame (S := S) Y).symm).trans ((whiskTail Y 2 g).trans (congrArg (· ⋙ raw Y g) (tail2Frame (S := S) Y)))
abbrev rTail (x : Total Y (power S 4).dest) := (gLift (S := S) (U := power S 2) (V := power S 1) Y f).app ((inner Y g).obj x)
abbrev lTail (x : Total Y (power S 4).dest) := (raw Y g).map ((wideArrow Y f).app x)
end
end ContextualComposition.GrothendieckStep.AmbientTerminalCones
