module
public import ContextualComposition.EvalPayload
/-! Mixed coherence for the strict-fibre decoder, and a separate common-target cancellation criterion. The native evaluation cube requires an additional inner pasting equation. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.DecoderCube
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage FibreValue
universe b w u v
variable {B : Type b} [Category.{w} B] {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z)
theorem mappedLift {A D : B} (a : A ⟶ D) (x : (proj Y).Fiber D) :
    Pure (payloadMap ((ChainPayload.fibreMap T (𝟭 B)).map (Reindex.lift (choice Y) a x))) :=
  ⟨_,PayloadLift.mapLiftPayload T (𝟭 B) x.val _⟩
theorem squarePure {A D : B} (a : A ⟶ D) (x : (proj Y).Fiber D) :
    Pure (payloadMap (((PayloadLift.square T (𝟭 B) (𝟭 B) baseChoice a).hom.app x).val)) := by
  let y := (PayloadLift.action T (𝟭 B) (𝟭 B) D).obj x
  apply payloadPureCancel (g := Reindex.lift (choice Z) a y)
  · exact (congrArg (fun f => FibreValue.Pure (payloadMap f)) (PayloadLift.square_fac T (𝟭 B) (𝟭 B) baseChoice a x)).mpr (mappedLift T a x)
  · exact chosenPure Z a y
theorem decodedPure {A D : B} (a : A ⟶ D) (x : (proj Y).Fiber D) :
    Pure ((value Z A).map ((PayloadLift.square T (𝟭 B) (𝟭 B) baseChoice a).hom.app x)) :=
  valuePure Z _ (squarePure T a x)
theorem natural {A D : B} (a : A ⟶ D) :
    (Y.map a.op).toFunctor ⋙ (T.app (op A)).toFunctor =
      (T.app (op D)).toFunctor ⋙ (Z.map a.op).toFunctor :=
  congrArg Cat.Hom.toFunctor (T.naturality a.op)
theorem mixed {A D : B} (a : A ⟶ D) (x : (proj Y).Fiber D) :
    (value Z A).map ((PayloadLift.square T (𝟭 B) (𝟭 B) baseChoice a).hom.app x) ≫
      (FibreValue.valueSquare Z a).hom.app ((PayloadLift.action T (𝟭 B) (𝟭 B) D).obj x) ≫
      (Z.map a.op).toFunctor.map (eqToHom (Functor.congr_obj (EvalPayload.valueSquare T D) x)) =
    eqToHom (Functor.congr_obj (EvalPayload.valueSquare T A) ((Reindex.functor (choice Y) a).obj x)) ≫
      (T.app (op A)).toFunctor.map ((FibreValue.valueSquare Y a).hom.app x) ≫
      eqToHom (Functor.congr_obj (natural T a) ((value Y D).obj x)) := by
  apply pureEq
  · exact pureComp (decodedPure T a x) (pureComp ⟨_,valueApp Z a _⟩ (pureMap _ ⟨_,rfl⟩))
  · exact pureComp ⟨_,rfl⟩ (pureComp (pureMap _ ⟨_,valueApp Y a x⟩) ⟨_,rfl⟩)
variable {P : Endpoints.{b,w,u,v} B} (S : P.Split)
theorem iterateMixed (n : Nat) {A D : B} (a : A ⟶ D) (x : (proj (Evaluation.G S Y n)).Fiber D) :
    (value (Evaluation.G S Z n) A).map ((PayloadLift.iterateSquare T S n a).hom.app x) ≫
      (FibreValue.valueSquare (Evaluation.G S Z n) a).hom.app ((PayloadLift.action (ChainPayload.layerMap T S (n+1)) (𝟭 B) (𝟭 B) D).obj x) ≫
      ((Evaluation.G S Z n).map a.op).toFunctor.map (eqToHom (Functor.congr_obj (EvalPayload.valueSquare (ChainPayload.layerMap T S (n+1)) D) x)) =
    eqToHom (Functor.congr_obj (EvalPayload.valueSquare (ChainPayload.layerMap T S (n+1)) A) ((Reindex.functor (Evaluation.iterateChoice S Y n) a).obj x)) ≫
      ((ChainPayload.layerMap T S (n+1)).app (op A)).toFunctor.map ((FibreValue.valueSquare (Evaluation.G S Y n) a).hom.app x) ≫
      eqToHom (Functor.congr_obj (natural (ChainPayload.layerMap T S (n+1)) a) ((value (Evaluation.G S Y n) D).obj x)) :=
  mixed (ChainPayload.layerMap T S (n+1)) a x

namespace CommonLift
variable {K : Type*} [Category* K] {p : K ⥤ B} {A D : B} {a : A ⟶ D}
theorem compare (R : Route p a) {s s' : p.Fiber A} {t t' : p.Fiber D}
    (l : s ⟶ R.act.obj t) (r : s' ⟶ R.act.obj t') (u : s ⟶ s') (v : t ⟶ t')
    (f : s.val ⟶ t.val) (g : s'.val ⟶ t'.val) (hl : l.val ≫ R.lift t = f)
    (hr : r.val ≫ R.lift t' = g) (h : f ≫ v.val = u.val ≫ g) :
    l ≫ R.act.map v = u ≫ r := by
  apply R.cancel
  change (l.val ≫ (R.act.map v).val) ≫ R.lift t' = (u.val ≫ r.val) ≫ R.lift t'
  rw [Category.assoc,R.natural,← Category.assoc,hl,Category.assoc,hr,h]
end CommonLift
end ContextualComposition.GrothendieckStep.DecoderCube
