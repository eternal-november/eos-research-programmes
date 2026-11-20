module
public import ContextualComposition.StrictTelCategories
public import ContextualComposition.NativeTriple
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelNativeFaces
open CategoryTheory SpanApex NativeBlocks NativeBlocks.Nested NativeAssoc
open StrictSpanAlgebra StrictTelAlgebra StrictTelRecovery
universe b w
set_option backward.isDefEq.respectTransparency false
variable {B : Type b} [Category.{max b w} B] {P : Endpoints.{b,max b w,b,max b w} B} (S : P.Split)

/-- The length-one outer word, rather than the empty word, is the left
unit of actual native two-level flattening. -/
theorem outerSingleton : outer S 1 ⋙ flatten S = 𝟭 (tel S) := flatten_single S

/-- Singleton inner blocks, retaining any outer length, give the other
unit of the native monad. -/
theorem innerSingletons : singletons S ⋙ flatten S = 𝟭 (tel S) := singletons_flatten S

/-- Both orders of genuine native three-level flattening agree. -/
theorem associative : Three.mergeRows S ⋙ flatten S = Three.mapRows S ⋙ flatten S := Three.flatten_assoc S

/-- The empty path plays a different role: applying the algebra to it
produces the contextad unit, whereas applying it to length one is identity. -/
theorem actionUnits (A : Algebra S) :
    (incl S 0 ⋙ A.action.functor = (read S A).operations.unit.functor) ∧
    (incl S 1 ⋙ A.action.functor = 𝟭 _) := ⟨rfl,A.equations.singleton⟩

variable {X : Type b} [Category.{max b w} X]

/-- The head–tail (right comb) formula for the actual native action
agrees strictly with the implemented left comb, on every diagram. -/
theorem rightComb (M : Contextad (power S 1)) (G : X ⥤ Apex P) (q : Path S X)
    (h : G ⋙ right P S = src S q) :
    tagged S (NativeAssoc.join S (single S G) q h) ⋙ (write S M).action.functor =
      StrictSpanAlgebra.join M.operations G (StrictTelFold.read S M.operations q)
        (h.trans (StrictTelFold.read_src S M.operations q).symm) := by
  exact (StrictTelFold.read_join S M.operations M.laws _ q h).trans
     (joinEq M.operations (Functor.comp_id G) rfl)

end ContextualComposition.GrothendieckStep.StrictTelNativeFaces
