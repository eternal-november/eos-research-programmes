module
public import ContextualComposition.ContextadInsideCells
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadInsideCells
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue ContextadRoutes ContextadLawTransport BoundaryPaste TelescopeSquares
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (k : Nat) {i j : Nat} {r s : Map S i j} (a : Cell r s)
theorem prefixPure (x) : Pure ((blocks S k j).first.map ((insideCell k a).grade.hom.app x)) := by
  apply alignPure ((castIsoApp (normalize k r) (normalize k s).symm (core k a) x).map (blocks S k j).first)
  let z := (blocks S k i).cutFunctor.obj x
  let t := (SuffixCell.alongIsoCell (power S k).dest (power S i).source (power S j).source r.over s.over a.grade (midVertical a)).hom.app z
  change Pure (((blocks S k j).joinFunctor ⋙ (blocks S k j).first).map t)
  rw [(blocks S k j).join_first]
  exact pureId _
theorem restAligned (x) : Aligned ((blocks S k j).rest.map ((insideCell k a).grade.hom.app x)) (a.grade.hom.app ((blocks S k i).rest.obj x)) := by
  apply ((castIsoApp (normalize k r) (normalize k s).symm (core k a) x).map (blocks S k j).rest).trans
  exact NativeCube.functorAlign (blocks S k j).join_rest _
end ContextualComposition.GrothendieckStep.ContextadInsideCells
