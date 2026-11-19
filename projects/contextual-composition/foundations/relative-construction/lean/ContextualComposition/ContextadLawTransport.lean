module
public import ContextualComposition.ContextadRoutes
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadLawTransport
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex FibreValue ContextadRoutes
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
universe u v
section Fiber
variable {K L B X : Type*} [Category* K] [Category* L] [Category* B] [Category* X]
variable {p : K ⥤ B} {q : L ⥤ B}
theorem pureLift {A : B} {a b : q.Fiber A} (f : a.val ⟶ b.val) (h : Pure (q.map f)) : q.IsHomLift (𝟙 A) f := by
  apply IsHomLift.of_fac' q _ _ a.property b.property
  exact pureEq h (pureComp ⟨_,rfl⟩ (pureComp (pureId _) ⟨_,rfl⟩))
theorem pureInverse {a b : L} (i : a ≅ b) (h : Pure (q.map i.hom)) : Pure (q.map i.inv) := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,?_⟩
  apply (cancel_mono (q.map i.hom)).mp
  rw [← q.map_comp,i.inv_hom_id,q.map_id,he,eqToHom_trans,eqToHom_refl]
def vertical {A : B} (F G : X ⥤ q.Fiber A) (i : F ⋙ Fiber.fiberInclusion ≅ G ⋙ Fiber.fiberInclusion)
    (h : ∀ x, Pure (q.map (i.hom.app x))) : F ≅ G where
  hom := { app := fun x => ⟨i.hom.app x,pureLift _ (h x)⟩, naturality := fun _ _ f => Subtype.ext (i.hom.naturality f) }
  inv := { app := fun x => ⟨i.inv.app x,pureLift _ (pureInverse (i.app x) (h x))⟩, naturality := fun _ _ f => Subtype.ext (i.inv.naturality f) }
  hom_inv_id := NatTrans.ext (funext fun x => Subtype.ext (i.hom_inv_id_app x))
  inv_hom_id := NatTrans.ext (funext fun x => Subtype.ext (i.inv_hom_id_app x))
theorem castPure {D : Type*} [Category* D] (p : L ⥤ D) {F F' G G' : X ⥤ L}
    (e : F' = F) (d : G = G') (i : F ≅ G) (h : ∀ x, Pure (p.map (i.hom.app x))) (x : X) :
    Pure (p.map ((eqToIso e ≪≫ i ≪≫ eqToIso d).hom.app x)) := by
  subst F'; subst G'; simpa using h x
def onFiber (F G : K ⥤ L) (hF : F ⋙ q = p) (hG : G ⋙ q = p) (i : F ≅ G)
    (h : ∀ x, Pure (q.map (i.hom.app x))) (A : B) :
    SpanPayload.fibreFunctor F q hF A ≅ SpanPayload.fibreFunctor G q hG A :=
  vertical _ _ (eqToIso (SpanPayload.fibre_diagram F q hF A) ≪≫ isoWhiskerLeft Fiber.fiberInclusion i ≪≫
    eqToIso (SpanPayload.fibre_diagram G q hG A).symm)
    (castPure q _ _ _ (fun x => h x.val))
end Fiber
section Conjugate
variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
variable (a : A ⥤ D) (b : B ⥤ E) (c : C ⥤ F) [a.IsIso] [b.IsIso]
noncomputable abbrev conjugate (f : A ⥤ B) := a.strictInv ⋙ f ⋙ b
theorem conjugateComp (f : A ⥤ B) (g : B ⥤ C) :
    conjugate a b f ⋙ conjugate b c g = conjugate a c (f ⋙ g) :=
  congrArg (fun V => (a.strictInv ⋙ f) ⋙ V ⋙ (g ⋙ c)) b.asIsomorphism.unit_eq.symm
theorem conjugateId : conjugate a a (𝟭 _) = 𝟭 _ := a.asIsomorphism.counit_eq
end Conjugate
section Native
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
abbrev raw {i j} (r : Map S i j) := restrict Y _ _ r.grade r.leg
noncomputable abbrev global {i j} (r : Map S i j) := conjugate (BlockEvaluation.global S Y i) (BlockEvaluation.global S Y j) (raw Y r)
theorem over {i j} (r : Map S i j) : global Y r ⋙ proj (PackedFree.pow S Y j) = proj (PackedFree.pow S Y i) :=
  (congrArg ((BlockEvaluation.global S Y i).strictInv ⋙ raw Y r ⋙ ·) (BlockEvaluation.globalOver S Y j)).trans
     ((congrArg ((BlockEvaluation.global S Y i).strictInv ⋙ ·) (ContextadCartesian.weightedOver _ _ _ _ _ r.over)).trans
       (BoundaryPaste.invOver _ _ _ (BlockEvaluation.globalOver S Y i)))
noncomputable abbrev evaluate {i j} (r : Map S i j) (A : B) := ContextadTotal.localValue _ _ (global Y r) (over Y r) A
theorem evalIncl {i j} (r : Map S i j) (A : B) :
    evaluate Y r A ⋙ incl (PackedFree.pow S Y j) A = incl (PackedFree.pow S Y i) A ⋙ global Y r :=
  ContextadRecognition.genericIncl _ _ A _ _
theorem globalComp {i j k} (r : Map S i j) (s : Map S j k) : global Y r ⋙ global Y s = global Y (comp r s) :=
  (conjugateComp _ _ _ _ _).trans (congrArg (conjugate _ _) (restrict_paste Y _ _ _ _ _ r.leg s.leg).symm)
theorem globalId (i : Nat) : global Y (identity (S := S) i) = 𝟭 _ :=
  (congrArg (conjugate _ _) (restrict_id Y _)).trans (conjugateId _)
theorem evalComp {i j k} (r : Map S i j) (s : Map S j k) (A : B) :
    evaluate Y r A ⋙ evaluate Y s A = evaluate Y (comp r s) A := by
  apply ContextadFinal.cancelIncl (PackedFree.pow S Y k) A
  exact (congrArg (evaluate Y r A ⋙ ·) (evalIncl Y s A)).trans
    ((congrArg (· ⋙ global Y s) (evalIncl Y r A)).trans ((congrArg (incl _ A ⋙ ·) (globalComp Y r s)).trans (evalIncl Y _ A).symm))
theorem evalId (i : Nat) (A : B) : evaluate Y (identity (S := S) i) A = 𝟭 _ := by
  apply ContextadFinal.cancelIncl (PackedFree.pow S Y i) A
  exact (evalIncl Y _ A).trans (congrArg (incl _ A ⋙ ·) (globalId Y i))
theorem evalTensor (m : ContextadTotal.Native S) (A : B) :
    evaluate Y (tensor m) A = ContextadCoherence.actual m Y A := (ContextadFinal.identify m _ Y A (ContextadSpecialize.agrees m A)).symm
/-- A native iso over the incoming base satisfying the outgoing endpoint triangle. No presheaf occurs. -/
structure Cell {i j} (r s : Map S i j) where
  grade : r.grade ≅ s.grade
  source : ∀ x, Pure ((power S j).source.map (grade.hom.app x))
  endpoint : whiskerRight grade.hom (power S j).dest ≫ s.leg = r.leg
noncomputable def rawCell {i j} {r s : Map S i j} (a : Cell r s) : raw Y r ≅ raw Y s :=
  WeightedCells.weightIso Y _ _ a.grade a.endpoint
theorem rawVertical {i j} {r s : Map S i j} (a : Cell r s) (x) :
    Pure ((BlockEvaluation.proj S Y j).map ((rawCell Y a).hom.app x)) := by
  change Pure ((power S j).source.map (gradeMap ((rawCell Y a).hom.app x)))
  rw [show gradeMap ((rawCell Y a).hom.app x) = _ from WeightedCells.weightGrade Y _ _ a.grade a.endpoint x]
  exact a.source _
noncomputable def globalCell {i j} {r s : Map S i j} (a : Cell r s) : global Y r ≅ global Y s :=
  isoWhiskerLeft (BlockEvaluation.global S Y i).strictInv (isoWhiskerRight (rawCell Y a) (BlockEvaluation.global S Y j))
theorem globalVertical {i j} {r s : Map S i j} (a : Cell r s) (x) :
    Pure ((proj (PackedFree.pow S Y j)).map ((globalCell Y a).hom.app x)) := by
  let f := (rawCell Y a).hom.app ((BlockEvaluation.global S Y i).strictInv.obj x)
  change Pure ((BlockEvaluation.global S Y j ⋙ proj (PackedFree.pow S Y j)).map f)
  rw [BlockEvaluation.globalOver]
  exact rawVertical Y a _
noncomputable def evalCell {i j} {r s : Map S i j} (a : Cell r s) (A : B) : evaluate Y r A ≅ evaluate Y s A :=
  isoWhiskerLeft (embed _ A) (isoWhiskerRight
    (onFiber (global Y r) (global Y s) (over Y r) (over Y s) (globalCell Y a) (globalVertical Y a) A) (value _ A))
end Native
end ContextualComposition.GrothendieckStep.ContextadLawTransport
