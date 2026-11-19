module
public import ContextualComposition.ContextadRecognition
public import ContextualComposition.ContextadSpecialize
public import ContextualComposition.ContextadUnary
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadFinal
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage ContextadVertical ContextadRecognition
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
theorem cancelIncl {C B : Type*} [Category* C] [Category* B] (G : Bᵒᵖ ⥤ Cat.{v,u}) (A : B)
    (F K : C ⥤ G.obj (op A)) (h : F ⋙ FibreValue.incl G A = K ⋙ FibreValue.incl G A) : F = K := by
  have q := EvalPayload.cancelInclusion (F ⋙ FibreValue.embed G A) (K ⋙ FibreValue.embed G A) h
  exact (congrArg (F ⋙ ·) (FibreValue.embed_value G A).symm).trans
    ((congrArg (· ⋙ FibreValue.value G A) q).trans (congrArg (K ⋙ ·) (FibreValue.embed_value G A)))
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (m : ContextadTotal.Native S) (d : ContextadTensor.Data S) (Y : PackedCuts.Psh.{u,max u v,u,v} B)
theorem identify (A : B) (h : Agrees m d A) :
    ContextadTensor.binary d Y A = ContextadTotal.binary m Y A :=
  cancelIncl (PackedFree.pow S Y 1) A _ _ ((chartRecognition m d A Y h (ContextadUnary.recognition S A Y)).trans (localIncl m A Y).symm)
noncomputable def exterior {A D : B} (a : D ⟶ A) (hA : Agrees m d A) (hD : Agrees m d D) :
    ((PackedFree.pow S Y 2).map a.op).toFunctor ⋙ ContextadTensor.binary d Y D ≅
      ContextadTensor.binary d Y A ⋙ P.baseRestrict Y a :=
  eqToIso (congrArg (((PackedFree.pow S Y 2).map a.op).toFunctor ⋙ ·) (identify m d Y D hD)) ≪≫
    ContextadTotal.exterior m Y a ≪≫ eqToIso (congrArg (· ⋙ P.baseRestrict Y a) (identify m d Y A hA).symm)
noncomputable def nativeExterior {A D : B} (a : D ⟶ A) :=
  exterior m (ContextadSpecialize.data m) Y a (ContextadSpecialize.agrees m A) (ContextadSpecialize.agrees m D)
end ContextualComposition.GrothendieckStep.ContextadFinal
