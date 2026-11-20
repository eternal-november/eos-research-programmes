module
public import ContextualComposition.ContentRepresentable
public import ContextualComposition.ContentEndpointSquares
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentActualBend
open CategoryTheory CategoryTheory.Bicategory Opposite
open AmbientCoherentPseudomonad RepresentableKleisli ContentRepresentable
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1150000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} Bᵒᵖ} {S : P.Split} (T : Data S)
variable {A A' D D' : B}

noncomputable def strongArrow (f : KH S (op D) (op A)) :
    letI : Bicategory (PartOp (B := B)) := content T
    contentAt A ⟶ contentAt D := by
  letI : Bicategory (Corep (B := B)) := corepresentable T
  exact Quiver.Hom.op (X := corepAt D) (Y := corepAt A) (op f)

noncomputable def pureArrow (u : A ⟶ D) :
    letI : Bicategory (PartOp (B := B)) := content T
    contentAt A ⟶ contentAt D :=
  strongArrow T (pureK T u.op)

theorem readStrong (f : KH S (op D) (op A)) :
    (localEquivalence T (contentAt A) (contentAt D)).functor.obj (strongArrow T f) =
    ContentEndpointSquares.native (row f) := rfl

theorem readPure (u : A ⟶ D) :
    (localEquivalence T (contentAt A) (contentAt D)).functor.obj (pureArrow T u) =
      StructuredArrow.mk (Y := op (T.unit.grade (op D))) (u ≫ (T.unit.discharge (op D)).unop) := by
  have h := readStrong T (pureK T u.op)
  rw [pureKAt] at h
  exact h

/-- Actual mixed-endpoint cells in the 1-cell opposite. The fibre-co chart has
already been decoded; the final opposite sends a native cell to the same
directed cell between the same covariant objects. -/
noncomputable def bentChart (u : A ⟶ A') (v : D ⟶ D')
    (x : KH S (op D) (op A)) (y : KH S (op D') (op A')) :
    letI : Bicategory (PartOp (B := B)) := content T
    (strongArrow T x ≫ pureArrow T v ⟶ pureArrow T u ≫ strongArrow T y) ≃
      (compose T y (pureK T u.op) ⟶ compose T (pureK T v.op) x) := by
  letI : Bicategory (Corep (B := B)) := corepresentable T
  exact ⟨fun t => t.unop2.unop, fun t => Bicategory.Opposite.op2 t.op,
    fun _ => rfl, fun _ => rfl⟩

noncomputable def bent (u : A ⟶ A') (v : D ⟶ D')
    (x : KH S (op D) (op A)) (y : KH S (op D') (op A')) :
    letI : Bicategory (PartOp (B := B)) := content T
    (strongArrow T x ≫ pureArrow T v ⟶ pureArrow T u ≫ strongArrow T y) ≃
      ContentEndpointSquares.Square u v (ContentEndpointSquares.native (row x)) (ContentEndpointSquares.native (row y)) :=
  (bentChart T u v x y).trans (ContentEndpointSquares.bent T u v x y)

end ContextualComposition.GrothendieckStep.ContentActualBend
