module
public import ContextualComposition.ContentActualBend
public import ContextualComposition.ContentCovariantOperations
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentComposition
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory Opposite TelescopeSquares
open AmbientCoherentPseudomonad RepresentableKleisli ContentRepresentable ContentActualBend
open ContentCovariantOperations ContentCovariantGrothendieck
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1050000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} Bᵒᵖ} {S : P.Split} (T : Data S)
variable {A D E : B}
abbrev Native (A D : B) := ContentComma.Native P A D
abbrev dual (x : Native (P := P) A D) : ContentComma.Context P A D :=
  ((ContentComma.write P A D).obj x).unop

noncomputable def nativeComp :
    Native (P := P) A D × Native (P := P) D E ⥤ Native (P := P) A E :=
  @RepresentableComparisonTransport.Data.mult (PartOp (B := B)) (content T) (N (P := P)) _ (data T)
    (contentAt A) (contentAt D) (contentAt E)

/-- On objects the coherent comparison uses the original context composite
in precisely the reversed 1-cell order. No hom cell reversal is done here. -/
theorem dualCompose (x : Native (P := P) A D) (y : Native (P := P) D E) :
    (nativeComp T).obj (x,y) =
      (ContentComma.read P A E).obj (op ((RepresentableCommaComposition.comp T).obj (dual y,dual x))) := rfl

/-- Grade order: the *outgoing* content grade followed by the incoming
grade pushed along the outgoing arrow's body. -/
def chain (x : Native (P := P) A D) (y : Native (P := P) D E) : Chain P 2 (op E) :=
  .cons y.right.unop (.cons (((grades P).map y.hom).toFunctor.obj x.right).unop (.nil _))

def chunk (x : Native (P := P) A D) (y : Native (P := P) D E) : TensorChart (S := S) E :=
  SpanPayload.Power.gradeObj S 1 (op E) (chain x y)

theorem nativeFormula (x : Native (P := P) A D) (y : Native (P := P) D E) :
    (nativeComp T).obj (x,y) =
      StructuredArrow.mk (Y := output T E (chunk (S := S) x y))
        (x.hom ≫ (lift P y.hom).app x.right ≫ comparison T E (chunk (S := S) x y)) := by
  refine (dualCompose T x y).trans ?_
  have H := RepresentableCommaComposition.original T (dual y) (dual x)
  rw [H]
  unfold RepresentableCommaComposition.exactNative
  let a := (((ContextadSpecialize.data T.mult).delta (op E)).app (chunk (S := S) x y))
  let b := (P.lift y.hom.op).app x.right.unop
  let c := x.hom.op
  change StructuredArrow.mk (T := dest P E) (Y := output T E (chunk (S := S) x y)) (a ≫ b ≫ c).unop =
    StructuredArrow.mk (T := dest P E) (Y := output T E (chunk (S := S) x y)) (c.unop ≫ b.unop ≫ a.unop)
  rw [unop_comp,unop_comp,Category.assoc]

theorem nativeUnit (A : B) :
    @RepresentableComparisonTransport.Data.unit (PartOp (B := B)) (content T) (N (P := P)) _ (data T) (contentAt A) =
      StructuredArrow.mk (Y := gradeUnit T A) (insert T A) := by
  change ContentEndpointSquares.native (row (unit T (op A))) = _
  rw [identityAt]
  rfl

end ContextualComposition.GrothendieckStep.ContentComposition
