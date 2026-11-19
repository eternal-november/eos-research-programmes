module
public import ContextualComposition.ContextadDisjointComparison
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadDisjointCut
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadLawTransport
open NativeAssoc ContextadOuterCharts ContextadModification
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} (f g : Map S 2 1)
theorem exchangeUnique (p : gradeCart g) (x : (power S 4).apex)
    (k : ((lhs f g).grade ⋙ NativeAssoc.last S 1).obj x ⟶ ((rhs f g).grade ⋙ NativeAssoc.last S 1).obj x)
    (base : (left P).map k = eqToHom (Functor.congr_obj (sameBase f g) x))
    (factorization : k ≫ (rightCone f g).app x = (leftCone f g).app x) : k = (exchange f g p).hom.app x :=
  cancel (left P) ((rightCone f g).app x) (rightConeCart f g x) _ _
    (base.trans (factorOver (left P) (leftCone f g) (rightCone f g) (sameBase f g) (overCone f g) (rightConeCart f g) x).symm)
    (factorization.trans (exchangeFac f g p x).symm)
end ContextualComposition.GrothendieckStep.ContextadDisjointCut
