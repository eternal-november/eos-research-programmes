module
public import ContextualComposition.BlockCompositor
/-! The two actual degeneracies of a binary cut.  The native source inserts a
length-zero block at the indicated endpoint.  The packed target uses the two
unit maps of the packed monad, not its one-step generator. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.BlockUnits
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked PackedCuts
set_option backward.isDefEq.respectTransparency false
universe b w u v
inductive Side where
  | left | right
def shape : Side → Nat → Nat × Nat
  | .left, n => (0,n)
  | .right, n => (n,0)
section Packed
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split) (Y : Psh.{b,w,u,v} B) (A : B)
abbrev value := Iterates.Packed P S Y (op A)
abbrev insert : Side → value S Y A ⥤ CutCompositor.D S Y A
  | .left => ((PackedFree.inc S ((PackedFree.free S).obj Y) 0).app (op A)).toFunctor
  | .right => (((PackedFree.free S).map (PackedFree.inc S Y 0)).app (op A)).toFunctor
theorem erase (s : Side) : insert S Y A s ⋙ mu S Y A = 𝟭 _ := by
  cases s with
  | left => exact congrArg Cat.Hom.toFunctor (NatTrans.congr_app (PackedFree.zero_join S Y) (op A))
  | right => exact congrArg Cat.Hom.toFunctor (NatTrans.congr_app (PackedFree.join_right S Y) (op A))
theorem outer (x : CutCompositor.D S Y A) : (profile S Y A x).1 = x.1 := by
  obtain ⟨⟨⟨n,m⟩,z⟩,rfl⟩ := (rigid S Y A).functor.bijective_obj.surjective x
  exact congrArg Prod.fst (profile_at S Y A (n,m) z)
theorem insertShape (s : Side) (x : value S Y A) : profile S Y A ((insert S Y A s).obj x) = shape s x.1 := by
  have o := outer S Y A ((insert S Y A s).obj x)
  have k := (profile_length S Y A ((insert S Y A s).obj x)).trans (congrArg Sigma.fst (Functor.congr_obj (erase S Y A s) x))
  change _ + _ = x.1 at k
  cases s with
  | left =>
    change _ = 0 at o
    exact Prod.ext o (by change _ = x.1; omega)
  | right =>
    change _ = x.1 at o
    exact Prod.ext o (by change _ = 0; omega)
theorem wrongSide {x : value S Y A} (f : (insert S Y A .left).obj x ⟶ (insert S Y A .right).obj x) : x.1 = 0 := by
  have e := (insertShape S Y A .left x).symm.trans ((profile_map S Y A f).trans (insertShape S Y A .right x))
  exact (congrArg Prod.fst e).symm
end Packed
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : Psh.{u,max u v,u,v} B) (A : B)
abbrev single := Lift.value Y A (whole S)
def degeneracy : Side → Over (whole S) (pairSpan S)
  | .left => ⟨Strict.lift _ _ (leftLeg S ⋙ incl S 0) (𝟭 _) rfl,rfl,rfl⟩
  | .right => ⟨Strict.lift _ _ (𝟭 _) (rightLeg S ⋙ incl S 0) rfl,rfl,rfl⟩
abbrev identityOver (U : Span (B := B)) : Over U U := ⟨𝟭 _,rfl,rfl⟩
theorem weightedIdentity (U : Span (B := B)) : Lift.weighted (identityOver U) Y A = 𝟭 _ :=
  (Lift.total_eq Y (d := NativeCleavage.FibreTotal.endpoint U.dest U.source A) (J := 𝟭 _) (k := rfl) (BlockEvaluation.fibreId U.source A)).trans rfl
theorem nativeErase (s : Side) : Lift.weighted (degeneracy S s) Y A ⋙ Lift.weighted (two S) Y A = 𝟭 _ := by
  refine (Lift.weighted_comp _ _ _ _).trans ((Lift.weighted_eq _ Y A (G := identityOver _) ?_).trans (weightedIdentity Y A _))
  cases s with
  | left => exact NativeAssoc.Whole.left_unit S
  | right => exact NativeAssoc.Whole.right_unit S
def length (x : single S Y A) := (grade _ _ x).val.1
theorem key {U V : Span (B := B)} (F : Over U V) {D : Type*} (k : V.apex → D) (x : Lift.value Y A U) :
    k (grade _ _ ((Lift.weighted F Y A).obj x)).val = k (F.functor.obj (grade _ _ x).val) := by
  have p := Functor.congr_obj (SpanPayload.total_projection Y (Lift.grade F A) _ (Lift.endpoint F A)) x
  have q := Functor.congr_obj (SpanPayload.fibre_diagram F.functor V.source F.source A) (grade _ _ x)
  exact (congrArg (fun t => k t.val) p).trans (congrArg k q)
theorem nativeShape (s : Side) (x : single S Y A) :
    CutCompositor.tags S Y A ((Lift.weighted (degeneracy S s) Y A).obj x) = shape s (length S Y A x) := by
  cases s <;> exact key Y A (degeneracy S _) (fun w : (pairSpan S).apex => (w.fst.1,w.snd.1)) x
theorem evaluationLength (x : single S Y A) : ((evaluation S Y A).obj x).1 = length S Y A x := by
  let C := (collect (power S) Y A).asEquivalence
  let z := C.inverse.obj x
  have e := Functor.congr_obj (collect_at (power S) Y A z.1) z.2
  have k := key Y A (tag (power S) z.1) (fun w => w.1) z.2
  have t : length S Y A (C.functor.obj z) = z.1 := (congrArg (length S Y A) e).trans k
  exact t.symm.trans (CutCompositor.tagOf S (gradeMap (C.counitIso.hom.app x)).val)
abbrev J (s : Side) := Lift.weighted (degeneracy S s) Y A
noncomputable abbrev target (s : Side) := evaluation S Y A ⋙ insert S Y A s
noncomputable abbrev staged (s : Side) := J S Y A s ⋙ CutCompositor.stages S Y A
noncomputable abbrev fullPath (s : Side) := J S Y A s ⋙ CutCompositor.previous S Y A
theorem targetShape (s : Side) (x : single S Y A) :
    profile S Y A ((target S Y A s).obj x) = shape s (length S Y A x) :=
  (insertShape S Y A s _).trans (congrArg (shape s) (evaluationLength S Y A x))
theorem stagedShape (s : Side) (x : single S Y A) :
    profile S Y A ((staged S Y A s).obj x) = shape s (length S Y A x) :=
  (CutCompositor.independentProfile S Y A _).trans (nativeShape S Y A s x)
theorem fullShape (s : Side) (x : single S Y A) :
    profile S Y A ((fullPath S Y A s).obj x) = shape s (length S Y A x) :=
  (CutCompositor.profileComparison S Y A _).trans (nativeShape S Y A s x)
theorem targetErase (s : Side) : target S Y A s ⋙ mu S Y A = evaluation S Y A :=
  congrArg (evaluation S Y A ⋙ ·) (erase S Y A s)
set_option maxHeartbeats 1500000 in
theorem nativeContract (s : Side) : J S Y A s ⋙ CutCompositor.native S Y A = evaluation S Y A :=
  (congrArg (fun H => J S Y A s ⋙ H ⋙ evaluation S Y A) (actual S Y A)).trans
    (congrArg (· ⋙ evaluation S Y A) (nativeErase S Y A s))
/-- The bottom side is fixed in advance: apply the specified multiplication
square on the native degeneracy, contract natively, and insert the packed
unit-law transport backwards. -/
noncomputable def afterStaged (s : Side) : staged S Y A s ⋙ mu S Y A ≅ target S Y A s ⋙ mu S Y A :=
  isoWhiskerLeft (J S Y A s) (BlockCompositor.multiplicationSquare S Y A) ≪≫
    eqToIso ((nativeContract S Y A s).trans (targetErase S Y A s).symm)
noncomputable def afterFull (s : Side) : fullPath S Y A s ⋙ mu S Y A ≅ target S Y A s ⋙ mu S Y A :=
  isoWhiskerLeft (J S Y A s) (actualSquare S Y A) ≪≫
    eqToIso ((nativeContract S Y A s).trans (targetErase S Y A s).symm)
noncomputable def stagedUnit (s : Side) : staged S Y A s ≅ target S Y A s :=
  CutCompositor.liftIso S Y A _ _ (fun x => (stagedShape S Y A s x).trans (targetShape S Y A s x).symm) (afterStaged S Y A s)
noncomputable def fullUnit (s : Side) : fullPath S Y A s ≅ target S Y A s :=
  CutCompositor.liftIso S Y A _ _ (fun x => (fullShape S Y A s x).trans (targetShape S Y A s x).symm) (afterFull S Y A s)
theorem stagedTriangle (s : Side) :
    whiskerRight (stagedUnit S Y A s).hom (mu S Y A) = (afterStaged S Y A s).hom :=
  (CutCompositor.cells S Y A _ _ (fun x => (stagedShape S Y A s x).trans (targetShape S Y A s x).symm)).apply_symm_apply _
theorem fullTriangle (s : Side) :
    whiskerRight (fullUnit S Y A s).hom (mu S Y A) = (afterFull S Y A s).hom :=
  (CutCompositor.cells S Y A _ _ (fun x => (fullShape S Y A s x).trans (targetShape S Y A s x).symm)).apply_symm_apply _
theorem uniqueUnit (s : Side) (t : staged S Y A s ⟶ target S Y A s)
    (h : whiskerRight t (mu S Y A) = (afterStaged S Y A s).hom) : t = (stagedUnit S Y A s).hom :=
  (CutCompositor.cells S Y A _ _ (fun x => (stagedShape S Y A s x).trans (targetShape S Y A s x).symm)).injective
    (h.trans (stagedTriangle S Y A s).symm)
/-- The independently characterized units commute with the actual tagged
binary compositor *before* erasing the cut. -/
theorem compositorUnit (s : Side) :
    whiskerLeft (J S Y A s) (BlockCompositor.compositor S Y A).hom ≫ (fullUnit S Y A s).hom = (stagedUnit S Y A s).hom := by
  apply uniqueUnit
  ext x
  have h := NatTrans.congr_app (fullTriangle S Y A s) x
  change (mu S Y A).map (_ ≫ _) = _
  rw [Functor.map_comp]
  change (mu S Y A).map _ ≫ (mu S Y A).map ((fullUnit S Y A s).hom.app x) = _
  change (mu S Y A).map ((fullUnit S Y A s).hom.app x) = _ at h
  rw [h]
  exact (Category.assoc ..).symm
end ContextualComposition.GrothendieckStep.BlockUnits
