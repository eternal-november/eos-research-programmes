module
public import ContextualComposition.BlockEvaluation
@[expose] public section
namespace ContextualComposition.GrothendieckStep.CutCompositor
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks NativeBlocks.Nested NativePacked PackedCuts
set_option backward.isDefEq.respectTransparency false
universe b w u v
section Lifting
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split) (Y : Psh.{b,w,u,v} B) (A : B)
abbrev D := Iterates.Packed P S ((PackedFree.free S).obj Y) (op A)
-- The arrow criterion of the independent #210 review, now used to lift cells
-- between functors, not to assert fullness across different cuts.
noncomputable def arrows {x y : D S Y A} (h : profile S Y A x = profile S Y A y) :
    (x ⟶ y) ≃ ((mu S Y A).obj x ⟶ (mu S Y A).obj y) := by
  apply Equiv.ofBijective (mu S Y A).map
  refine ⟨(BlockCartesian.faithful _ (joinIncoming S Y A)).map_injective,?_⟩
  intro f
  obtain ⟨⟨z,g⟩,e⟩ := (joinIncoming S Y A y).surjective ⟨(mu S Y A).obj x,f⟩
  have zx := obj_ext S Y A ((profile_map S Y A g).trans h.symm) (congrArg Sigma.fst e)
  subst z
  exact ⟨g,(Sigma.mk.inj_iff.mp e).2.eq⟩
variable {X : Type*} [Category* X] (F G : X ⥤ D S Y A)
abbrev Same := ∀ x, profile S Y A (F.obj x) = profile S Y A (G.obj x)
noncomputable def liftCell (h : Same S Y A F G) (a : F ⋙ mu S Y A ⟶ G ⋙ mu S Y A) : F ⟶ G where
  app x := (arrows S Y A (h x)).symm (a.app x)
  naturality x y f := by
    let M := mu S Y A
    let _ : M.Faithful := BlockCartesian.faithful _ (joinIncoming S Y A)
    apply M.map_injective
    rw [M.map_comp,M.map_comp]
    exact ((congrArg (M.map (F.map f) ≫ ·) ((arrows S Y A (h y)).apply_symm_apply _)).trans
      (a.naturality f)).trans (congrArg (· ≫ M.map (G.map f)) ((arrows S Y A (h x)).apply_symm_apply _).symm)
noncomputable def cells (h : Same S Y A F G) : (F ⟶ G) ≃ (F ⋙ mu S Y A ⟶ G ⋙ mu S Y A) where
  toFun a := whiskerRight a (mu S Y A)
  invFun := liftCell S Y A F G h
  left_inv a := by ext x; exact (arrows S Y A (h x)).symm_apply_apply _
  right_inv a := by ext x; exact (arrows S Y A (h x)).apply_symm_apply _
noncomputable def liftIso (h : Same S Y A F G) (i : F ⋙ mu S Y A ≅ G ⋙ mu S Y A) : F ≅ G where
  hom := liftCell S Y A F G h i.hom
  inv := liftCell S Y A G F (fun x => (h x).symm) i.inv
  hom_inv_id := by
    ext x
    let M := mu S Y A
    let _ : M.Faithful := BlockCartesian.faithful _ (joinIncoming S Y A)
    apply M.map_injective
    change M.map (_ ≫ _) = M.map (𝟙 _)
    rw [M.map_comp,M.map_id]
    exact ((congrArg₂ (· ≫ ·) ((arrows S Y A (h x)).apply_symm_apply (i.hom.app x)) ((arrows S Y A (h x).symm).apply_symm_apply (i.inv.app x)))).trans (i.hom_inv_id_app x)
  inv_hom_id := by
    ext x
    let M := mu S Y A
    let _ : M.Faithful := BlockCartesian.faithful _ (joinIncoming S Y A)
    apply M.map_injective
    change M.map (_ ≫ _) = M.map (𝟙 _)
    rw [M.map_comp,M.map_id]
    exact ((congrArg₂ (· ≫ ·) ((arrows S Y A (h x).symm).apply_symm_apply (i.inv.app x)) ((arrows S Y A (h x)).apply_symm_apply (i.hom.app x)))).trans (i.inv_hom_id_app x)
end Lifting

open BlockEvaluation
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : Psh.{u,max u v,u,v} B) (A : B)
abbrev W := Lift.value Y A (pairSpan S)
def tags (x : W S Y A) : Nat × Nat :=
  let p := (grade _ _ x).val
  (p.fst.1,p.snd.1)
theorem tagOf {x y : tel S} (h : x ⟶ y) : x.1 = y.1 := by cases h; rfl
theorem invariant {x y : W S Y A} (f : x ⟶ y) : tags S Y A x = tags S Y A y :=
  Prod.ext (tagOf S (gradeMap f).val.hom.fst) (tagOf S (gradeMap f).val.hom.snd)
theorem onCut (i : Nat × Nat) (z : coords S Y A i) :
    tags S Y A ((nativeEquiv S Y A).functor.obj ⟨i,z⟩) = i := by
  let F := Lift.comp (cut S i) (tagged S i)
  have eo := Functor.congr_obj (native_at S Y A i) z
  change (nativeEquiv S Y A).functor.obj ⟨i,z⟩ = (Lift.weighted F Y A).obj z at eo
  rw [eo]
  have e1 := Functor.congr_obj (SpanPayload.total_projection Y (Lift.grade F A) _ (Lift.endpoint F A)) z
  have e2 := Functor.congr_obj (SpanPayload.fibre_diagram F.functor (pairSpan S).source F.source A) (grade _ _ z)
  let key (w : (pairSpan S).apex) := (w.fst.1,w.snd.1)
  exact (congrArg (fun t => key t.val) e1).trans (congrArg key e2)
theorem profileComparison (x : W S Y A) :
    PackedCuts.profile S Y A ((NativePacked.compare S Y A).functor.obj x) = tags S Y A x := by
  let N := nativeEquiv S Y A
  let z := N.inverse.obj x
  have lhs : PackedCuts.profile S Y A ((NativePacked.compare S Y A).functor.obj x) = z.1 :=
    PackedCuts.profile_at S Y A z.1 ((leaf S Y A z.1).functor.obj z.2)
  have rhs := onCut S Y A z.1 z.2
  exact lhs.trans (rhs.symm.trans (invariant S Y A (N.counitIso.hom.app x)))
theorem tags_at (i : Nat × Nat) : Sigma.incl (C := fun i => Lift.value Y A (fixed S i)) i ⋙ (tagsEquiv S Y A).functor =
    Lift.weighted (tagged S i) Y A :=
  (congrArg (· ⋙ Lift.weighted (untag S) Y A) (collect_at (fixed S) Y A i)).trans
    (Lift.weighted_comp (tag (fixed S) i) Y A (untag S))
theorem actual_tags (i : Nat × Nat) (z : Lift.value Y A (fixed S i)) :
    tags S Y A ((tagsEquiv S Y A).functor.obj ⟨i,z⟩) = i := by
  have eq := Functor.congr_obj (tags_at S Y A i) z
  change (tagsEquiv S Y A).functor.obj ⟨i,z⟩ = _ at eq
  rw [eq]
  let F := tagged S i
  let key (w : (pairSpan S).apex) := (w.fst.1,w.snd.1)
  have e1 := Functor.congr_obj (SpanPayload.total_projection Y (Lift.grade F A) _ (Lift.endpoint F A)) z
  have e2 := Functor.congr_obj (SpanPayload.fibre_diagram F.functor (pairSpan S).source F.source A) (grade _ _ z)
  exact (congrArg (fun t => key t.val) e1).trans (congrArg key e2)
theorem packProfile (i : Nat × Nat) (z : double S Y A i) :
    profile S Y A ((packing S Y A).functor.obj ⟨i,z⟩) = i := by
  let T := retag S Y A i
  have k := profile_at S Y A i (T.inverse.obj z)
  change profile S Y A ((packing S Y A).functor.obj ⟨i,T.functor.obj (T.inverse.obj z)⟩) = i at k
  exact (congrArg (fun t => profile S Y A ((packing S Y A).functor.obj ⟨i,t⟩)) (Functor.congr_obj T.counit_eq z).symm).trans k
theorem independentProfile (x : W S Y A) : profile S Y A ((blockwise S Y A).functor.obj x) = tags S Y A x := by
  let T := tagsEquiv S Y A
  let z := T.inverse.obj x
  exact (packProfile S Y A z.1 ((staged S Y A z.1).functor.obj z.2)).trans
    ((actual_tags S Y A z.1 z.2).symm.trans (invariant S Y A (T.counitIso.hom.app x)))
theorem sameProfile : Same S Y A (blockwise S Y A).functor (NativePacked.compare S Y A).functor :=
  fun x => (independentProfile S Y A x).trans (profileComparison S Y A x).symm
noncomputable abbrev stages := (blockwise S Y A).functor
noncomputable abbrev previous := (NativePacked.compare S Y A).functor
noncomputable abbrev native := Lift.weighted (row S) Y A ⋙ NativeCleavage.FibreTotal.into Y (BlockCartesian.All.dest S) (BlockCartesian.All.source S) A ⋙
  BlockCartesian.All.onFibre S Y A ⋙ NativeCleavage.FibreTotal.out Y (rightLeg S) (leftLeg S) A ⋙ evaluation S Y A
/-- Exact remaining obligation. A natural cell from separately evaluated blocks
after packed multiplication to the original native result has a unique lift
before multiplication, because the two actual comparisons preserve ordered cuts. -/
noncomputable def compositorCells : (stages S Y A ⟶ previous S Y A) ≃ (stages S Y A ⋙ multiplication S Y A ⟶ native S Y A) :=
  (cells S Y A _ _ (sameProfile S Y A)).trans (actualSquare S Y A).homToEquiv
noncomputable def compositorOfSquare (c : stages S Y A ⋙ multiplication S Y A ≅ native S Y A) : stages S Y A ≅ previous S Y A :=
  liftIso S Y A _ _ (sameProfile S Y A) (c ≪≫ (actualSquare S Y A).symm)
theorem reconstructed (c : stages S Y A ⋙ multiplication S Y A ≅ native S Y A) :
    whiskerRight (compositorOfSquare S Y A c).hom (multiplication S Y A) ≫ (actualSquare S Y A).hom = c.hom := by
  have h := (cells S Y A _ _ (sameProfile S Y A)).apply_symm_apply (c.hom ≫ (actualSquare S Y A).inv)
  exact (congrArg (· ≫ (actualSquare S Y A).hom) h).trans (by simp)
/-- Independent staging and the earlier full-word construction in their common
native coordinates. Only the first route uses the native cut on its input. -/
noncomputable abbrev cutEach (i : Nat × Nat) := (Lift.weighted (cut S i) Y A)
noncomputable abbrev first (i : Nat × Nat) := cutEach S Y A i ⋙ (staged S Y A i).functor
noncomputable abbrev second (i : Nat × Nat) := (leaf S Y A i).functor ⋙ (retag S Y A i).functor
theorem fibreRetract {C D E : Type*} [Category* C] [Category* D] [Category* E] {p : C ⥤ E} {q : D ⥤ E}
    (x : E) (F : C ⥤ D) (G : D ⥤ C) (h : F ⋙ q = p) (k : G ⋙ p = q) (e : F ⋙ G = 𝟭 C) :
    SpanPayload.fibreFunctor F q h x ⋙ SpanPayload.fibreFunctor G p k x = 𝟭 _ := by
  apply EvalPayload.cancelInclusion
  exact (EvalPayload.fibrePaste x F G h k).trans (congrArg (Functor.Fiber.fiberInclusion ⋙ ·) e)
theorem cancelCut {C D E K : Type*} [Category* C] [Category* D] [Category* E] [Category* K]
    (F : C ⥤ D) (I : D ⥤ E) (J : C ⥤ K) (P : K ⥤ E) (Q : E ⥤ K) (O : K ⥤ C)
    (h : F ⋙ I = J ⋙ P) (k : P ⋙ Q = 𝟭 _) (r : J ⋙ O = 𝟭 _) : F ⋙ I ⋙ Q ⋙ O = 𝟭 _ :=
  (congrArg (· ⋙ Q ⋙ O) h).trans ((congrArg (fun T => J ⋙ T ⋙ O) k).trans r)
theorem emptyMiddle (n : Nat) : cutEach S Y A (n,0) ⋙ middle S Y A n 0 = 𝟭 _ := by
  let U := cut S (n,0)
  let I := NativeCleavage.FibreTotal.into Y (fixed S (n,0)).dest (fixed S (n,0)).source A
  let J := NativeCleavage.FibreTotal.into Y (power S n).dest (power S n).source A
  let O := NativeCleavage.FibreTotal.out Y (power S n).dest (power S n).source A
  let Q := SpanPayload.fibreFunctor (suffix S Y n 0) (proj S Y n) (suffixOver S Y n 0) A
  have e : Lift.strict U Y A ⋙ Q = 𝟭 _ := fibreRetract A (Lift.total U Y) (suffix S Y n 0) (Lift.over U Y) (suffixOver S Y n 0) (emptySuffix S Y n)
  exact cancelCut _ I J (Lift.strict U Y A) Q O (Lift.into U Y A) e (NativeCleavage.FibreTotal.into_out_functors ..)
theorem emptySuffixCompositor (n : Nat) : first S Y A (n,0) = second S Y A (n,0) :=
  congrArg (· ⋙ (leaf S Y A (n,0)).functor) (emptyMiddle S Y A n)
noncomputable abbrev chart := ZeroPower.Sum.map (first S Y A) ⋙ (packing S Y A).functor
def removeTag {B C D E K : Type*} [Category* B] [Category* C] [Category* D] [Category* E] [Category* K]
    (F : B ⥤ C) (T : C ≌ D) (J : C ⥤ E) (M : E ⥤ K) (Z : B ⥤ E) (h : F ⋙ J = Z) :
    (F ⋙ T.functor) ⋙ (T.inverse ⋙ (J ⋙ M)) ≅ Z ⋙ M :=
  isoWhiskerLeft F (isoWhiskerRight T.unitIso.symm (J ⋙ M)) ≪≫ eqToIso (congrArg (· ⋙ M) h)
set_option maxHeartbeats 1000000 in
noncomputable def chartEq : (nativeEquiv S Y A).functor ⋙ stages S Y A ≅ chart S Y A :=
  removeTag (ZeroPower.Sum.map (cutEach S Y A)) (tagsEquiv S Y A) (ZeroPower.Sum.map (fun i => (staged S Y A i).functor))
    (packing S Y A).functor (ZeroPower.Sum.map (first S Y A)) (PayloadLaws.sumComp _ _).symm
theorem oldChart : ZeroPower.Sum.map (second S Y A) ⋙ (packing S Y A).functor = (packedEquiv S Y A).functor :=
  congrArg (· ⋙ (packing S Y A).functor) (PayloadLaws.sumComp _ _)
def undoChart {C D R : Type*} [Category* C] [Category* D] [Category* R] (N : C ≌ D) (F : D ⥤ R) (G : C ⥤ R)
    (q : N.functor ⋙ F ≅ G) : F ≅ N.inverse ⋙ G :=
  isoWhiskerRight N.counitIso.symm F ≪≫ isoWhiskerLeft N.inverse q
set_option maxHeartbeats 800000 in
/-- A family of natural isomorphisms to the separately defined full-word
evaluations, one per ordered pair and natural in the whole weighted fixed-length
fibre, suffices. No extra compatibility across different tags is presumed. -/
noncomputable def ofFixed (h : ∀ i, first S Y A i ≅ second S Y A i) : stages S Y A ≅ previous S Y A := by
  let N := nativeEquiv S Y A
  let M := (packing S Y A).functor
  let z : ZeroPower.Sum.map (first S Y A) ≅ ZeroPower.Sum.map (second S Y A) :=
    Sigma.natIso fun i => isoWhiskerRight (h i) (Sigma.incl (C := double S Y A) i)
  let q := chartEq S Y A ≪≫ isoWhiskerRight z M ≪≫ eqToIso (oldChart S Y A)
  exact undoChart N (stages S Y A) (packedEquiv S Y A).functor q
end ContextualComposition.GrothendieckStep.CutCompositor
