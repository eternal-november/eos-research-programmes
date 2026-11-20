module
public import ContextualComposition.RepresentableCompositionComparison
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableCommaComposition
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open RepresentableKleisli RepresentableNativeComposition AmbientCoherentPseudomonad ContextadSpecialize TelescopeSquares
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable {A D E : B} (T : Data S)
abbrev N (A D : B) := CostructuredArrow (P.extend A) D
abbrev decode (A D : B) := (commaEquiv (S := S) (A := A) (D := D)).functor
abbrev encode (A D : B) := (commaEquiv (S := S) (A := A) (D := D)).inverse
noncomputable def comp : N (P := P) A D × N (P := P) D E ⥤ N (P := P) A E :=
  (encode (S := S) A D).prod (encode (S := S) D E) ⋙ composeFunctor T ⋙ decode (S := S) A E
noncomputable def comparison :
    composeFunctor T ⋙ decode (S := S) A E ≅ ((decode (S := S) A D).prod (decode (S := S) D E)) ⋙ comp T :=
  transport ((decode (S := S) A D).prod (decode (S := S) D E)) ((encode (S := S) A D).prod (encode (S := S) D E))
    (composeFunctor T ⋙ decode (S := S) A E)
    (NatIso.prod (commaEquiv (S := S) (A := A) (D := D)).unitIso (commaEquiv (S := S) (A := D) (D := E)).unitIso)
def operand (x : N (P := P) A D) (y : N (P := P) D E) : Chain P 2 A :=
  .cons x.left (.cons ((P.grades.map x.hom.op).toFunctor.obj y.left) (.nil _))
noncomputable def exactNative (x : N (P := P) A D) (y : N (P := P) D E) : N (P := P) A E :=
  let q := SpanPayload.Power.gradeObj S 1 A (operand x y)
  let m := data T.mult
  CostructuredArrow.mk (Y := (m.tensor A).obj q) ((m.delta A).app q ≫ ((P.lift x.hom).app y.left ≫ y.hom))
theorem original (x : N (P := P) A D) (y : N (P := P) D E) :
    (comp T).obj (x,y) = exactNative T x y :=
  let p := (RepresentableComma.write (P.extend A) D).obj x
  let q := (RepresentableComma.write (P.extend D) E).obj y
  congrArg (RepresentableComma.read (P.extend A) E).obj ((nativeObject T p q).trans (tensorFormula T p q))
end ContextualComposition.GrothendieckStep.RepresentableCommaComposition
