module
public import ContextualComposition.ContentCovariantGrothendieck
public import ContextualComposition.RepresentableKleisliOperations
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentCovariantOperations
open CategoryTheory CategoryTheory.Functor Opposite TelescopeSquares SpanApex
open AmbientBicategory AmbientHorizontalFrames AmbientCoherentPseudomonad RepresentableKleisliOperations
open ContentCovariantGrothendieck
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1150000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} Bᵒᵖ} {S : P.Split}

abbrev o (Y : Dual (B := B)) : Obj.{u,u} Bᵒᵖ := Y
def Q (Y : Dual (B := B)) : Cov (B := B) := decode (underlying.{u,u} (obj S 1 (o Y)))

/-- In the split presentation one layer is the covariant integral, with its
actual covariant base action given by the same cocartesian comparison. -/
def fibre (Y : Dual (B := B)) (A : B) : CategoryTheory.IsoCat ((Q (S := S) Y).obj A) (Row P Y A) :=
  rowIso P Y A

theorem mapAt (Y : Dual (B := B)) {A D : B} (v : A ⟶ D) :
    (fibre (S := S) Y A).inverse ⋙ ((Q (S := S) Y).map v).toFunctor ⋙ (fibre (S := S) Y D).functor =
      ContentCovariantGrothendieck.restrict P Y v := rfl

variable (T : Data S)
def gradeUnit (A : B) : (grades P).obj A := op (T.unit.grade (op A))
def insert (A : B) : A ⟶ (dest P A).obj (gradeUnit T A) :=
  (T.unit.discharge (op A)).unop

noncomputable def unitAtRow (Y : Dual (B := B)) (A : B) :
    (decode Y).obj A ⥤ Row P Y A :=
  (AmbientRoundTrip.compAt (E S (o Y) T.unit).hom (op A)).op ⋙ (fibre (S := S) Y A).functor

theorem unitPayload (Y : Dual (B := B)) (A : B) (y : (decode Y).obj A) :
    (unitAtRow T Y A).obj y = ContentCovariantGrothendieck.pair P Y (gradeUnit T A) (((decode Y).map (insert T A)).toFunctor.obj y) := by
  change (fibre (S := S) Y A).functor.obj (op ((AmbientRoundTrip.compAt (E S (o Y) T.unit).hom (op A)).obj y.unop)) = _
  rw [unitAt T (o Y) (op A)]
  rfl

abbrev TensorChart (A : B) := (SpanApex.chainSource S 1).Fiber (op A)
noncomputable def output (A : B) (t : TensorChart (S := S) A) : (grades P).obj A :=
  op (((ContextadSpecialize.data T.mult).tensor (op A)).obj t)
noncomputable def comparison (A : B) (t : TensorChart (S := S) A) :
    ((SpanPayload.Power.chainsEndpoint S 1 (op A)).obj t).unop ⟶ (dest P A).obj (output T A t) :=
  (((ContextadSpecialize.data T.mult).delta (op A)).app t).unop

noncomputable def multiplyAtRow (Y : Dual (B := B)) (A : B) :
    (decode (underlying.{u,u} (obj S 2 (o Y)))).obj A ⥤ Row P Y A :=
  (AmbientRoundTrip.compAt (M S (o Y) T.mult).hom (op A)).op ⋙ (fibre (S := S) Y A).functor

/-- The actual multiplication map pushes the payload forward through native
accumulation. The comparison appears once, with no inverse or co-Kleisli leg. -/
theorem multiplyPayload (Y : Dual (B := B)) (A : B) (t : Chain P 2 (op A))
    (y : (decode Y).obj ((endpoint t).unop)) :
    (multiplyAtRow T Y A).obj (op (realize Y S t y.unop)) =
      ContentCovariantGrothendieck.pair P Y (output T A (SpanPayload.Power.gradeObj S 1 (op A) t))
        (((decode Y).map (comparison T A (SpanPayload.Power.gradeObj S 1 (op A) t))).toFunctor.obj y) := by
  change (fibre (S := S) Y A).functor.obj (op ((AmbientRoundTrip.compAt (M S (o Y) T.mult).hom (op A)).obj
    (realize Y S t y.unop))) = _
  rw [mulAt T (o Y) (op A),ContextadTensor.binaryObj]
  rfl

end ContextualComposition.GrothendieckStep.ContentCovariantOperations
