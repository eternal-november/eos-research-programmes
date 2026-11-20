module
public import ContextualComposition.AmbientObservedCell
public import ContextualComposition.AmbientInsideLetters
public import ContextualComposition.ContextadExchangeUnique
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientExchangeFactors
open CategoryTheory CategoryTheory.Functor Opposite FibreValue TelescopeSquares ContextadRoutes SpanApex NativeBlocks
open ContextadDisjointCut ContextadLawTransport ContextadModification AmbientExchangeDemand AmbientCoordinates AmbientBicategory
open AmbientDisjointFrames ContextadCellWhisker
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (f g : Map S 2 1) (p : gradeCart g) (t : (power S 4).apex)
abbrev TailArrow := ((lhs f g).grade ⋙ NativeAssoc.last S 1).obj t ⟶ ((rhs f g).grade ⋙ NativeAssoc.last S 1).obj t
def Factors (w : TailArrow f g t) : Prop :=
  (left P).map w = eqToHom (Functor.congr_obj (sameBase f g) t) ∧ w ≫ (rightCone f g).app t = (leftCone f g).app t
variable {A D : (power S 2).apex} (v : A ⟶ D)
def Tests : Prop := Pure (gradeMap v) ∧ ∃ w : TailArrow f g t, Aligned ((NativeAssoc.last S 1).map v) w ∧ Factors f g t w
theorem gradeIff (a : A = (lhs f g).grade.obj t) (b : D = (rhs f g).grade.obj t) :
    Aligned v ((assembled f g p).hom.app t) ↔ Tests f g t v := by
  let G := (assembled f g p).hom.app t
  let e := (exchange f g p).hom.app t
  constructor
  · intro h
    exact ⟨AmbientMateCalculus.pureOfAligned (h.map gradeProjection) (assembledHead f g p t),e,
      (h.map (NativeAssoc.last S 1)).trans (NativeCube.ofEq (assembledTip f g p t)),
      (exchangePure f g p t).choose_spec,exchangeFac f g p t⟩
  · rintro ⟨h,w,vw,c⟩
    have we := exchangeUnique f g p t w c.1 c.2
    have z := vw.trans ((NativeCube.ofEq we).trans (NativeCube.ofEq (assembledTip f g p t)).symm)
    exact AmbientInsideLetters.alignParts P.grades (right P S) a b v G h (assembledHead f g p t) z
end ContextualComposition.GrothendieckStep.AmbientExchangeFactors
