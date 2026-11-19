module
public import ContextualComposition.ContextadUnit
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadTensor
open CategoryTheory CategoryTheory.Functor Opposite TelescopeSquares SpanApex SpanPayload.Power
universe b w u v
set_option backward.isDefEq.respectTransparency false
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split)
/-- Accumulation on actual two-stage grade squares in each source fibre. No base-change or monad laws. -/
structure Data where
  tensor : ∀ A : B, (chainSource S 1).Fiber A ⥤ P.grades.obj (op A)
  delta : ∀ A : B, tensor A ⋙ P.extend A ⟶ chainsEndpoint S 1 A
variable {S} (d : Data S) (Y : Bᵒᵖ ⥤ Cat.{max u v,u})
abbrev rows (A : B) := pack S 1 A Y ⋙ restrict Y _ _ (d.tensor A) (d.delta A)
def points (n : Nat) (A : B) :
    Fibre.asCat (Y := Y) S n A ≃ Σ t : Chain P n A, Y.obj (op (endpoint t)) :=
  ⟨fun x => ⟨x.chain,x.value⟩,fun z => ⟨z.1,z.2⟩,fun _ => rfl,fun _ => rfl⟩
instance chartIso (n : Nat) (A : B) : (Fibre.comparison (Y := Y) S n A).IsIso where
  bijective_obj := ((points (S := S) Y n A).trans (realizedEquiv Y S n A)).bijective
noncomputable def binary (A : B) := (Fibre.comparison (Y := Y) S 2 A).strictInv ⋙ rows d Y A
theorem read (A : B) : Fibre.comparison S 2 A ⋙ binary d Y A = rows d Y A :=
  congrArg (· ⋙ rows d Y A) (Fibre.comparison (Y := Y) S 2 A).asIsomorphism.unit_eq.symm
theorem binaryObj (A : B) (t : Chain P 2 A) (y : Y.obj (op (endpoint t))) :
    (binary d Y A).obj (realize Y S t y) =
      pair Y _ ((d.tensor A).obj (gradeObj S 1 A t)) ((Y.map ((d.delta A).app (gradeObj S 1 A t)).op).toFunctor.obj y) :=
  Functor.congr_obj (read d Y A) ⟨t,y⟩
theorem rows_natural {Z : Bᵒᵖ ⥤ Cat.{max u v,u}} (T : Y ⟶ Z) (A : B) :
    rows d Y A ⋙ ChainPayload.fibreMap T _ = ChainPayload.onFibre T S 2 A ⋙ rows d Z A :=
  (congrArg (pack S 1 A Y ⋙ ·) (ChainPayload.base_square T _ _ (d.tensor A) (d.delta A))).trans
    (congrArg (· ⋙ restrict Z _ _ (d.tensor A) (d.delta A)) (pack_natural S 1 A Y T))
theorem binary_natural {Z : Bᵒᵖ ⥤ Cat.{max u v,u}} (T : Y ⟶ Z) (A : B) :
    binary d Y A ⋙ ChainPayload.fibreMap T _ =
      ((ChainPayload.layerMap T S 2).app (op A)).toFunctor ⋙ binary d Z A := by
  apply (Fibre.comparison (Y := Y) S 2 A).asIsomorphism.functor_comp_injective
  exact (congrArg (· ⋙ ChainPayload.fibreMap T _) (read d Y A)).trans
    ((rows_natural d Y T A).trans ((congrArg (ChainPayload.onFibre T S 2 A ⋙ ·) (read d Z A).symm).trans
    (congrArg (· ⋙ binary d Z A) (ChainPayload.comparison_square T S 2 A))))
theorem rowsGrade (A : B) {x z : Fibre.asCat (Y := Y) S 2 A} (f : x ⟶ z) :
    gradeMap ((rows d Y A).map f) = (d.tensor A).map (gradeMap ((pack S 1 A Y).map f)) := rfl
theorem rowsPayload (A : B) {x z : Fibre.asCat (Y := Y) S 2 A} (f : x ⟶ z) :
    payloadMap ((rows d Y A).map f) =
      (Y.map ((d.delta A).app (gradeObj S 1 A x.chain)).op).toFunctor.map (payloadMap ((pack S 1 A Y).map f)) ≫
        eqToHom (endpoint_square Y _ _ (d.tensor A) (d.delta A) (gradeMap ((pack S 1 A Y).map f)) z.value) :=
  restrict_payload _ _ _ _ _ _
/-- Exact remaining base-change test, reflected along a strict arrow-faithful chart. -/
theorem baseChange_iff {A D : B} (a : D ⟶ A) :
    ((Iterates.layer P S Y 2).map a.op).toFunctor ⋙ binary d Y D = binary d Y A ⋙ P.baseRestrict Y a ↔
    Fibre.pullFunctor S a ⋙ rows d Y D = rows d Y A ⋙ P.baseRestrict Y a := by
  have l : Fibre.comparison S 2 A ⋙ (((Iterates.layer P S Y 2).map a.op).toFunctor ⋙ binary d Y D) =
      Fibre.pullFunctor S a ⋙ rows d Y D :=
    (congrArg (· ⋙ binary d Y D) (Fibre.comparison_square (Y := Y) (n := 2) S a).symm).trans
      (congrArg (Fibre.pullFunctor S a ⋙ ·) (read d Y D))
  have r := congrArg (· ⋙ P.baseRestrict Y a) (read d Y A)
  exact ⟨fun h => l.symm.trans ((congrArg (Fibre.comparison S 2 A ⋙ ·) h).trans r),
    fun h => (Fibre.comparison (Y := Y) S 2 A).asIsomorphism.functor_comp_injective (l.trans (h.trans r.symm))⟩
end ContextualComposition.GrothendieckStep.ContextadTensor
