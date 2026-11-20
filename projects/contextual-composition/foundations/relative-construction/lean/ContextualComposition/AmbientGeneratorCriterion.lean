module
public import ContextualComposition.AmbientExchangeDemand
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientGeneratorCriterion
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadLawTransport ContextadCellPasting ContextadHorizontalLaws AmbientHorizontalRead
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (n : Nat)
inductive Matches : {r s : Map S n 1} → Path r s → {f g : obj S n X ⟶ obj S 1 X} → (f ⟶ g) → Prop
  | one {r s} {c : Cell r s} {f g} {u : f ⟶ g} (h : Reads u c) : Matches (.one c) u
  | more {r s t} {c : Cell r s} {p : Path s t} {f g k} {u : f ⟶ g} {v : g ⟶ k} (h : Reads u c) (w : Matches p v) :
      Matches (.more c p) (u ≫ v)
variable {X n}
theorem sound {r s : Map S n 1} {p : Path r s} {f g : obj S n X ⟶ obj S 1 X} {u : f ⟶ g} (w : Matches X n p u) : Reads u (composite p) := by
  induction w with
  | one h => exact h
  | more h _ ih => exact vertical h ih
theorem transfer {r s : Map S n 1} {p q : Path r s} {f g : obj S n X ⟶ obj S 1 X} {u v : f ⟶ g}
    (a : Matches X n p u) (b : Matches X n q v) (e : ∀ x, (composite p).grade.hom.app x = (composite q).grade.hom.app x) : u = v := by
  have l := sound a
  have h := sound b
  rw [sameCell _ _ e] at l
  exact extRaw S (fun x => (l x).trans (h x).symm)
end ContextualComposition.GrothendieckStep.AmbientGeneratorCriterion
