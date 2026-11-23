module
public import ContextualComposition.TelescopeAmbientLeaf

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeValueLift
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open NativeCleavage NativeBlocks SpanApex CoproductSpan CoproductSpan.All
open FibreValue TelescopeSquares ContextadAmbientPayload AmbientBicategory AmbientCoordinates
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v

private theorem pure_before {C : Type*} [Category* C] {x y z : C}
    (q : x ⟶ y) (r : y ⟶ z) (hq : Pure q) : Aligned (q ≫ r) r := by
  obtain ⟨rfl,rfl⟩ := hq
  exact NativeCube.ofEq (Category.id_comp r)

section Value
variable {B : Type u} [Category.{v} B] (H : Bᵒᵖ ⥤ Cat.{v,u}) {A D : B} (a : A ⟶ D)

theorem value_lift (z : (proj H).Fiber D) :
    Aligned ((incl H A).map ((valueSquare H a).hom.app z) ≫ FibreValue.arrow H a ((value H D).obj z))
      (Reindex.lift (choice H) a z) := by
  apply (pure_before _ _ (pureMap (incl H A) (show Pure ((valueSquare H a).hom.app z) from ⟨_,valueApp _ _ _⟩))).trans
  exact (AmbientDescentRecognition.chosen H a z).symm

theorem included_value {z z' : (proj H).Fiber A} (m : z ⟶ z') :
    Aligned ((incl H A).map ((value H A).map m)) m.val :=
  (NativeCube.functorAlign (value_embed H A) m).map (Functor.Fiber.fiberInclusion (p := proj H) (S := A))
theorem value_factorization {s : (proj H).Fiber A} (z : (proj H).Fiber D)
    (m : s ⟶ (Reindex.functor (choice H) a).obj z)
    {j k : Total H (𝟭 B)} (g : j ⟶ k) (h : Aligned (m.val ≫ Reindex.lift (choice H) a z) g) :
    Aligned ((incl H A).map ((value H A).map m ≫ (valueSquare H a).hom.app z) ≫
      FibreValue.arrow H a ((value H D).obj z)) g := by
  rw [Functor.map_comp,Category.assoc]
  exact ((included_value H m).comp (value_lift H a z)).trans h

set_option linter.defProp false in
def value_face {K : Type*} [Category* K] {p : K ⥤ B} (R : Route p a)
    (F : K ⥤ Total H (𝟭 B)) (over : F ⋙ proj H = p)
    (face : NativeCube.Face R (Route.ofChoice (choice H) a) F over) (x : p.Fiber D) :=
  value_factorization H a ((SpanPayload.fibreFunctor F (proj H) over D).obj x)
    (face.sq.hom.app x) (F.map (R.lift x)) (face.fac x)

theorem pasted_value_lift {C E : Type*} [Category* C] [Category* E]
    (U : C ⥤ E) (F : C ⥤ (proj H).Fiber D) (F' : E ⥤ (proj H).Fiber A)
    (i : U ⋙ F' ≅ F ⋙ Reindex.functor (choice H) a) (x : C)
    {k l : Total H (𝟭 B)} (g : k ⟶ l)
    (fac : Aligned ((i.hom.app x).val ≫ Reindex.lift (choice H) a (F.obj x)) g) :
    Aligned ((incl H A).map ((SpanPayload.pasteIso i.symm (valueSquare H a).symm).symm.hom.app x) ≫
      FibreValue.arrow H a ((value H D).obj (F.obj x))) g := by
  have split := FinalCube.Mix.pasteComponent
    (F := F) (G := value H D) (F' := F') (G' := value H A) (U := U)
    (V := Reindex.functor (choice H) a) (W := (H.map a.op).toFunctor) i (valueSquare H a) x
  rw [← split]
  exact value_factorization H a (F.obj x) (i.hom.app x) g fac

set_option linter.defProp false in
def pasted_chosen_face {K C : Type*} [Category* K] [Category* C] {p : K ⥤ B}
    (R : Route p a) (F : K ⥤ Total H (𝟭 B)) (over : F ⋙ proj H = p)
    (face : NativeCube.Face R (Route.ofChoice (choice H) a) F over)
    (J : C ⥤ p.Fiber D) (x : C) :=
  pasted_value_lift H a (J ⋙ R.act) (J ⋙ SpanPayload.fibreFunctor F (proj H) over D)
    (SpanPayload.fibreFunctor F (proj H) over A) (isoWhiskerLeft J face.sq) x
    (F.map (R.lift (J.obj x))) (face.fac (J.obj x))

end Value

variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (X : Obj.{u,v} B) {A D : B} (a : A ⟶ D)

set_option linter.defProp false in
/-- Component formula of the actual positive evaluation comparison. -/
def positive_paste_data (n : Nat) (x : Total (underlying X) (SpanPayload.Power.nativeEndpoint S n D)) :=
  (FinalCube.Mix.pasteComponent
    (F := Evaluation.onFibre S (underlying X) n D)
    (G := value (Evaluation.G S (underlying X) n) D)
    (F' := Evaluation.onFibre S (underlying X) n A)
    (G' := value (Evaluation.G S (underlying X) n) A)
    (U := nativeReindex (underlying X) S n a)
    (V := Reindex.functor (Evaluation.iterateChoice S (underlying X) n) a)
    (W := ((Evaluation.G S (underlying X) n).map a.op).toFunctor)
    (Evaluation.fibreSquare S (underlying X) n a)
    (valueSquare (Evaluation.G S (underlying X) n) a) x).symm

set_option linter.defProp false in
def positive_raw_lift (n : Nat) (x : Total (underlying X) (SpanPayload.Power.nativeEndpoint S n D)) :=
  value_face (Evaluation.G S (underlying X) n) a
    (Route.ofChoice (payloadChoice (underlying X) S n) a)
    (Evaluation.nativeFunctor S (underlying X) n) (Evaluation.native_over S (underlying X) n)
    (NativeCube.evaluation S (underlying X) n a)
    ((FibreTotal.into (underlying X) (positivePowers P S n).dest (positivePowers P S n).source D).obj x)

set_option linter.defProp false in
set_option maxHeartbeats 350000 in
def positive_pasted_lift (n : Nat) (x : Total (underlying X) (SpanPayload.Power.nativeEndpoint S n D)) :=
  pasted_chosen_face (Evaluation.G S (underlying X) n) a
    (Route.ofChoice (payloadChoice (underlying X) S n) a)
    (Evaluation.nativeFunctor S (underlying X) n) (Evaluation.native_over S (underlying X) n)
    (NativeCube.evaluation S (underlying X) n a)
    (FibreTotal.into (underlying X) (positivePowers P S n).dest (positivePowers P S n).source D) x

end ContextualComposition.GrothendieckStep.TelescopeValueLift
