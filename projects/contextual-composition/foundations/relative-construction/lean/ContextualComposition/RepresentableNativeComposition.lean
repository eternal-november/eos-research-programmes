module
public import ContextualComposition.RepresentableKleisliPins
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableNativeComposition
open CategoryTheory CategoryTheory.Functor Opposite TelescopeSquares
open CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientCoherentPseudomonad RepresentableKleisli RepresentableKleisliOperations
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable {A D E : B}
abbrev Row (A D : B) := RepresentableComma.Row (P.extend A) D
abbrev tail (E : B) := underlying.{u,u} (KObj S E)
def body (x : Row (P := P) A D) := RepresentableComma.body (P.extend A) D x
def input (x : Row (P := P) A D) (y : Row (P := P) D E) : (underlying.{u,u} (obj.{u,u} S 2 (yObj E))).obj (op A) :=
  pair (tail (S := S) E) (P.extend A) (grade _ _ x) ((P.baseRestrict (RepresentableYoneda.rep E) (body x)).obj y)
noncomputable def result (T : Data S) (x : Row (P := P) A D) (y : Row (P := P) D E) : Row (P := P) A E :=
  (ContextadTensor.binary (ContextadSpecialize.data T.mult) (RepresentableYoneda.rep E) A).obj (input (S := S) x y)
theorem layerAt (y : Row (P := P) D E) (x : Row (P := P) A D) :
    (AmbientRoundTrip.compAt (AmbientBicategory.map S 1 (canonical (S := S) y)).hom A).obj x =
    input (S := S) x y := by
  change (AmbientRoundTrip.compAt (ContextadAmbientPayload.blockStrong (S := S) (canonical (S := S) y).hom 1) A).obj x = _
  rw [canon_eq,layerStrict]
  rfl
theorem actualAt (T : Data S) (f : KH S A D) (y : Row (P := P) D E) :
    row (compose T f (canonical (S := S) y)) = result T (row f) y := by
  change (AmbientRoundTrip.compAt (M S (yObj E) T.mult).hom A).obj
      ((AmbientRoundTrip.compAt (AmbientBicategory.map S 1 (canonical (S := S) y)).hom A).obj (row f)) = _
  rw [mulAt,layerAt]
  rfl
def chain (x : Row (P := P) A D) (y : Row (P := P) D E) : Chain P 2 A :=
  let p := grade _ _ x
  let q := (P.grades.map (body x).op).toFunctor.obj (grade _ _ y)
  .cons p (.cons q (.nil _))
def finalBody (x : Row (P := P) A D) (y : Row (P := P) D E) : endpoint (chain x y) ⟶ E :=
  (P.lift (body x)).app (grade _ _ y) ≫ body y
theorem tensorFormula (T : Data S) (x : Row (P := P) A D) (y : Row (P := P) D E) :
    result T x y =
      let z := SpanPayload.Power.gradeObj S 1 A (chain x y)
      let t := ContextadSpecialize.data T.mult
      pair (RepresentableYoneda.rep E) (P.extend A) ((t.tensor A).obj z)
        (Discrete.mk ((t.delta A).app z ≫ finalBody x y)) :=
  ContextadTensor.binaryObj (ContextadSpecialize.data T.mult) (RepresentableYoneda.rep E) A (chain x y) (Discrete.mk (finalBody x y))
end ContextualComposition.GrothendieckStep.RepresentableNativeComposition
