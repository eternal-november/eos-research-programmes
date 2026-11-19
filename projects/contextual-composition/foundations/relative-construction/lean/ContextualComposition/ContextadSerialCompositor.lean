module
public import ContextualComposition.ContextadEvaluatedWhisker
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadEvaluatedWhisker
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex TelescopeSquares
open ContextadRoutes ContextadLawTransport ContextadCellWhisker
set_option backward.isDefEq.respectTransparency false
universe u v
theorem matchIso {U V : Type*} [Category* U] [Category* V] {F G F' G' : U ⥤ V}
    (a : F ≅ G) (b : F' ≅ G') (l : F = F') (r : G' = G) (h : ∀ x, Aligned (a.hom.app x) (b.hom.app x)) :
    a = eqToIso l ≪≫ b ≪≫ eqToIso r := by
  cases l; cases r; apply Iso.ext; apply NatTrans.ext; funext x
  simpa using (h x).eq
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) {i j k l : Nat} {f g : Map S j k} (a : Cell f g)
theorem evalBeforeIso (p : Map S i j) (A : B) :
    evalCell Y (before a p) A =
      eqToIso (evalComp Y p f A).symm ≪≫ isoWhiskerLeft (evaluate Y p A) (evalCell Y a A) ≪≫ eqToIso (evalComp Y p g A) :=
  matchIso _ _ _ _ (evalBefore Y a p A)
theorem evalAfterIso (q : Map S k l) (A : B) :
    evalCell Y (after a q) A =
      eqToIso (evalComp Y f q A).symm ≪≫ isoWhiskerRight (evalCell Y a A) (evaluate Y q A) ≪≫ eqToIso (evalComp Y g q A) :=
  matchIso _ _ _ _ (evalAfter Y a q A)
end ContextualComposition.GrothendieckStep.ContextadEvaluatedWhisker
