module
public import ContextualComposition.ContextadVertical
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadSpecialize
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage SpanApex NativeBlocks ContextadVertical SpanPayload.Power
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (m : ContextadTotal.Native S) (A : B)
theorem fibreInject {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D)
    {p : C ⥤ E} (q : D ⥤ E) (h : F ⋙ q = p) (a : E) (i : Function.Injective F.obj) :
    Function.Injective (SpanPayload.fibreFunctor F q h a).obj := by
  intro x y e
  apply Subtype.ext
  apply i
  have t := Functor.congr_obj (SpanPayload.fibre_diagram F q h a)
  exact (t x).symm.trans ((congrArg Subtype.val e).trans (t y))
instance chartIso : (gradeFunctor S 1 A).IsIso where
  bijective_obj := ⟨fibreInject _ _ _ A (powerPoints S 1).decode.injective,
    SpanPayload.fibre_obj_surjective _ _ _ A (powerPoints S 1).decode.surjective⟩
abbrev nativeFibre := SpanPayload.fibreFunctor m.grade (power S 1).source m.over A
noncomputable abbrev grade := (gradeFunctor S 1 A).strictInv ⋙ nativeFibre m A ⋙ FibreValue.value P.grades A
theorem gradeSpec : inclusion (S := S) A ⋙ m.grade = gradeFunctor S 1 A ⋙ grade m A ⋙ ContextadChart.one (P := P) A := by
  let J := nativeFibre m A
  let I := Functor.Fiber.fiberInclusion (p := (power S 1).source) (S := A)
  have v : J ⋙ I = (J ⋙ FibreValue.value P.grades A) ⋙ ContextadChart.one (P := P) A :=
    congrArg (fun U => J ⋙ U ⋙ I) (FibreValue.value_embed P.grades A).symm
  exact (SpanPayload.fibre_diagram m.grade _ m.over A).symm.trans (v.trans
    (congrArg (· ⋙ J ⋙ FibreValue.value P.grades A ⋙ ContextadChart.one (P := P) A) (gradeFunctor S 1 A).asIsomorphism.unit_eq))
theorem left : (gradeFunctor S 1 A ⋙ (grade m A ⋙ P.extend A)) =
    (inclusion (S := S) A ⋙ m.grade ⋙ (power S 1).dest) :=
  (congrArg (gradeFunctor S 1 A ⋙ grade m A ⋙ ·) (ContextadChart.oneEnd S A).symm).trans
    (congrArg (· ⋙ (power S 1).dest) (gradeSpec m A).symm)
noncomputable def verticalCell : gradeFunctor S 1 A ⋙ (grade m A ⋙ P.extend A) ⟶ gradeFunctor S 1 A ⋙ chainsEndpoint S 1 A :=
  eqToHom (left m A) ≫ whiskerLeft (inclusion (S := S) A) m.delta ≫ eqToHom (gradeEndpoint S 1 A).symm
noncomputable def delta : grade m A ⋙ P.extend A ⟶ chainsEndpoint S 1 A :=
  ((whiskeringLeft _ _ B).obj (gradeFunctor S 1 A)).preimage (verticalCell m A)
theorem deltaSpec : whiskerLeft (gradeFunctor S 1 A) (delta m A) = verticalCell m A :=
  Functor.map_preimage ((whiskeringLeft _ _ B).obj (gradeFunctor S 1 A)) (verticalCell m A)
noncomputable def data : ContextadTensor.Data S := ⟨grade m,delta m⟩
theorem whiskerCast {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D)
    {G H : D ⥤ E} (e : G = H) : whiskerLeft F (eqToHom e) = eqToHom (congrArg (F ⋙ ·) e) := by
  subst H; simp
theorem trim {C : Type*} [Category* C] {x x' y y' : C} (h : x'=x) (q : y=y') (f : x ⟶ y) :
    HEq (eqToHom h ≫ f ≫ eqToHom q) f := by subst x'; subst y'; simp
theorem agrees : Agrees m (data m) A where
  grade := gradeSpec m A
  endpoint := by
    have t : HEq (verticalCell m A) (whiskerLeft (inclusion (S := S) A) m.delta) := trim _ _ _
    apply t.symm.trans
    symm
    unfold localLeg pasteLift
    rw [whiskerLeft_comp,whiskerCast,whiskerCast]
    rw [Category.assoc]
    exact (trim _ _ _).trans (heq_of_eq (deltaSpec m A))
end ContextualComposition.GrothendieckStep.ContextadSpecialize
