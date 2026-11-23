module
public import ContextualComposition.RepresentableComma
public import ContextualComposition.ContentComma

/-! Generic factorization in the coherent native context and content
presentations. Identity-body generics determine the named grade. The body
of their composite retains the noninvertible structural comparison. -/

@[expose] public section
namespace ContextualComposition.GrothendieckStep.MarkedGenericFactorizations
open CategoryTheory Opposite
open ContextadRepresentable TelescopeSquares SpanPayload.Power
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B]

section Context
variable {P : Endpoints.{u,u,u,u} B} (S : P.Split)
variable {A D : B}

def kappa (A : B) (p : P.grades.obj (op A)) : CostructuredArrow (P.extend A) ((P.extend A).obj p) :=
  CostructuredArrow.mk (Y := p) (𝟙 _)

theorem context_factor (x : CostructuredArrow (P.extend A) D) :
    (CostructuredArrow.map x.hom).obj (kappa A x.left) = x := by
  refine CostructuredArrow.obj_ext _ _ rfl ?_
  simp [kappa]

def unitProbe (d : ContextadUnit.Data P) (A : B) : CostructuredArrow (P.extend A) A :=
  (RepresentableComma.read (P.extend A) A).obj
    ((((ContextadUnit.unit d S).app (rep A)).app (op A)).toFunctor.obj (Discrete.mk (𝟙 A)))

theorem marked_context_unit (d : ContextadUnit.Data P) (A : B) :
    unitProbe S d A = (CostructuredArrow.map (d.discharge A)).obj (kappa A (d.grade A)) := by
  unfold unitProbe
  rw [ContextadRepresentable.unit]
  refine CostructuredArrow.obj_ext _ _ ?_ ?_
  · rfl
  change (P.extend A).map (eqToHom _) ≫ (𝟙 _ ≫ d.discharge A) = d.discharge A ≫ 𝟙 _
  simp

noncomputable def binaryProbe (d : ContextadTensor.Data S) (t : Chain P 2 A) :
    CostructuredArrow (P.extend A) (endpoint t) :=
  (RepresentableComma.read (P.extend A) (endpoint t)).obj <|
    (ContextadTensor.binary d (rep (endpoint t)) A).obj (realize (rep _) S t (Discrete.mk (𝟙 (endpoint t))))

theorem marked_context_binary (d : ContextadTensor.Data S) (t : Chain P 2 A) :
    binaryProbe S d t = (CostructuredArrow.map ((d.delta A).app (gradeObj S 1 A t))).obj
      (kappa A ((d.tensor A).obj (gradeObj S 1 A t))) := by
  unfold binaryProbe
  rw [ContextadRepresentable.tensor]
  refine CostructuredArrow.obj_ext _ _ ?_ ?_
  · rfl
  change (P.extend A).map (eqToHom _) ≫ (𝟙 _ ≫ _) = _ ≫ 𝟙 _
  simp

end Context

section Content
open ContentCovariantGrothendieck
variable {P : Endpoints.{u,u,u,u} Bᵒᵖ} (S : P.Split)
variable {A D : B}

def gamma (D : B) (q : (grades P).obj D) : ContentComma.Native P ((dest P D).obj q) D :=
  StructuredArrow.mk (Y := q) (𝟙 _)

theorem content_factor (x : ContentComma.Native P A D) :
    (StructuredArrow.map x.hom).obj (gamma D x.right) = x := by
  refine StructuredArrow.obj_ext _ _ rfl ?_
  simp [gamma]

theorem marked_content_unit (d : ContextadUnit.Data P) (A : B) :
    (ContentComma.read P A A).obj (op (unitProbe S d (op A))) =
      (StructuredArrow.map (d.discharge (op A)).unop).obj (gamma A (op (d.grade (op A)))) := by
  rw [marked_context_unit]
  refine StructuredArrow.obj_ext _ _ ?_ ?_
  · rfl
  change (𝟙 _ ≫ _).unop ≫ (dest P A).map (eqToHom _) = _ ≫ 𝟙 _
  simp

theorem marked_content_binary (d : ContextadTensor.Data S) (t : Chain P 2 (op D)) :
    (ContentComma.read P (endpoint t).unop D).obj (op (binaryProbe S d t)) =
      (StructuredArrow.map ((d.delta (op D)).app (gradeObj S 1 (op D) t)).unop).obj
        (gamma D (op ((d.tensor (op D)).obj (gradeObj S 1 (op D) t)))) := by
  rw [marked_context_binary]
  refine StructuredArrow.obj_ext _ _ ?_ ?_
  · rfl
  change (𝟙 _ ≫ _).unop ≫ (dest P D).map (eqToHom _) = _ ≫ 𝟙 _
  simp

end Content
end ContextualComposition.GrothendieckStep.MarkedGenericFactorizations
