module
public import ContextualComposition.PackedCuts
public import ContextualComposition.NativeTriple
@[expose] public section
namespace ContextualComposition.GrothendieckStep.NativePacked
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage NativeBlocks NativeBlocks.Nested SpanApex
universe u v j l
variable {B : Type u} [Category.{max u v} B]
namespace Lift
variable {U V W : Span (B := B)} (F : Over U V)
abbrev grade (A : B) := SpanPayload.fibreFunctor F.functor V.source F.source A
theorem endpoint (A : B) : grade F A ⋙ FibreTotal.endpoint V.dest V.source A = FibreTotal.endpoint U.dest U.source A := by
  change (grade F A ⋙ Functor.Fiber.fiberInclusion) ⋙ V.dest = _
  rw [SpanPayload.fibre_diagram]
  exact congrArg (Functor.Fiber.fiberInclusion ⋙ ·) F.dest
variable (Y : Bᵒᵖ ⥤ Cat.{l,j}) (A : B)
abbrev value (U : Span (B := B)) := Total Y (FibreTotal.endpoint U.dest U.source A)
def weighted : value Y A U ⥤ value Y A V := SpanPayload.totalMap Y (grade F A) _ (endpoint F A)
def total := SpanPayload.totalMap Y F.functor V.dest F.dest
theorem over : total F Y ⋙ FibreTotal.projection Y V.dest V.source = FibreTotal.projection Y U.dest U.source :=
  (congrArg (· ⋙ V.source) (SpanPayload.total_projection Y F.functor V.dest F.dest)).trans (congrArg (gradeProjection ⋙ ·) F.source)
abbrev strict := SpanPayload.fibreFunctor (total F Y) (FibreTotal.projection Y V.dest V.source) (over F Y) A
theorem total_eq {K M : Type*} [Category* K] [Category* M] {e : K ⥤ B} {d : M ⥤ B} {H J : K ⥤ M}
    (p : H = J) {h : H ⋙ d = e} {k : J ⋙ d = e} : SpanPayload.totalMap Y H d h = SpanPayload.totalMap Y J d k := by subst J; rfl
theorem global : weighted F Y A ⋙ SpanPayload.Power.fibreInclude A Y V.source V.dest =
    SpanPayload.Power.fibreInclude A Y U.source U.dest ⋙ total F Y :=
  (SpanPayload.total_comp Y (grade F A) _ (endpoint F A) Functor.Fiber.fiberInclusion V.dest rfl).trans
    ((total_eq Y (SpanPayload.fibre_diagram F.functor V.source F.source A)).trans
      (SpanPayload.total_comp Y Functor.Fiber.fiberInclusion _ rfl F.functor V.dest F.dest).symm)
theorem into : weighted F Y A ⋙ FibreTotal.into Y V.dest V.source A = FibreTotal.into Y U.dest U.source A ⋙ strict F Y A := by
  apply EvalPayload.cancelInclusion
  exact (global F Y A).trans (congrArg (FibreTotal.into Y U.dest U.source A ⋙ ·)
    (SpanPayload.fibre_diagram (total F Y) (FibreTotal.projection Y V.dest V.source) (over F Y) A).symm)
theorem back : FibreTotal.into Y U.dest U.source A ⋙ strict F Y A ⋙ FibreTotal.out Y V.dest V.source A = weighted F Y A := by
  have k : weighted F Y A ⋙ (FibreTotal.into Y V.dest V.source A ⋙ FibreTotal.out Y V.dest V.source A) = weighted F Y A := rfl
  exact (congrArg (· ⋙ FibreTotal.out Y V.dest V.source A) (into F Y A).symm).trans k
def comp (G : Over V W) : Over U W := ⟨F.functor ⋙ G.functor,(congrArg (F.functor ⋙ ·) G.source).trans F.source,
  (congrArg (F.functor ⋙ ·) G.dest).trans F.dest⟩
theorem weighted_comp (G : Over V W) : weighted F Y A ⋙ weighted G Y A = weighted (comp F G) Y A := by
  apply (SpanPayload.total_comp Y (grade F A) _ (endpoint F A) (grade G A) _ (endpoint G A)).trans
  apply total_eq
  apply EvalPayload.cancelInclusion
  exact (EvalPayload.fibrePaste A F.functor G.functor F.source G.source).trans
    (SpanPayload.fibre_diagram (comp F G).functor W.source (comp F G).source A).symm
theorem weighted_eq {G : Over U V} (e : F.functor = G.functor) : weighted F Y A = weighted G Y A := by
  cases F; cases G; congr
theorem equivOfIso [F.functor.IsIso] : (weighted F Y A).IsEquivalence := by
  let _ := F.functor.asIsomorphism.toEquivalence.isEquivalence_functor
  let _ : (grade F A).IsEquivalence := SpanPayload.fibre_isEquivalence _ _ _ A F.functor.bijective_obj.surjective
  exact SpanPayload.totalIsEquivalence _ _ _ _
end Lift

variable {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
abbrev pairSpan := product (whole S) (whole S)
abbrev fixed (i : Nat × Nat) := product (power S i.1) (power S i.2)
abbrev full (i : Nat × Nat) := power S (i.1+i.2)
noncomputable def cut (i : Nat × Nat) : Over (full S i) (fixed S i) :=
  ⟨(blocks S i.1 i.2).cutFunctor,(blocks S i.1 i.2).source,(blocks S i.1 i.2).dest⟩
theorem cutEquivalence (Y : Bᵒᵖ ⥤ Cat.{l,j}) (A : B) (i : Nat × Nat) : (Lift.weighted (cut S i) Y A).IsEquivalence := by
  let _ : (cut S i).functor.IsIso := (blocks S i.1 i.2).strictIso.isIso_functor
  exact Lift.equivOfIso _ _ _
noncomputable abbrev two : Over (pairSpan S) (whole S) := ⟨binary S,binary_source S,binary_dest S⟩
abbrev row : Over (pairSpan S) (NativeAssoc.Three.rows S) := ⟨outer S 2,rfl,rfl⟩
abbrev tagged (i : Nat × Nat) : Over (fixed S i) (pairSpan S) := ⟨tagPair S i,rfl,rfl⟩
abbrev inclPower (n : Nat) : Over (power S n) (whole S) := ⟨incl S n,rfl,rfl⟩
theorem cut_rejoin (i : Nat × Nat) :
    (Lift.comp (Lift.comp (cut S i) (tagged S i)) (two S)).functor = (inclPower S (i.1+i.2)).functor := rejoin S _ _
theorem two_flatten : (Lift.comp (row S) (NativeAssoc.Three.flattenOver S)).functor = (two S).functor := flatten_two S
section Tags
variable {I : Type} (U : I → Span (B := B)) (Y : Bᵒᵖ ⥤ Cat.{l,j}) (A : B)
abbrev taggedSpan : Span (B := B) := ⟨Cat.of (Σ i, (U i).apex),Sigma.desc (fun i => (U i).source),Sigma.desc (fun i => (U i).dest)⟩
abbrev tag (i : I) : Over (U i) (taggedSpan U) := ⟨Sigma.incl (C := fun i => (U i).apex) i,rfl,rfl⟩
abbrev collect := CoproductSpan.compare (fun i => (U i).source) (fun i => (U i).dest) A Y
theorem collect_at (i : I) : Sigma.incl (C := fun i => Lift.value Y A (U i)) i ⋙ collect U Y A = Lift.weighted (tag U i) Y A := by
  let p := fun i => (U i).source
  let d := fun i => (U i).dest
  exact SpanPayload.total_comp Y (Sigma.incl (C := fun i => (p i).Fiber A) i) _ rfl (CoproductSpan.pack p A) _ (CoproductSpan.over p d A)
end Tags
def untag : Over (taggedSpan (fixed S)) (pairSpan S) :=
  ⟨gatherPairs S,PackedFree.sigma_ext fun _ => rfl,PackedFree.sigma_ext fun _ => rfl⟩
def untagIso : IsoCat (parts S) (pairs S) := ⟨gatherPairs S,splitPairs S,(gather_split S).symm,split_gather S⟩
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B)
abbrev coords (i : Nat × Nat) := Lift.value Y A (full S i)
noncomputable def nativeEquiv : (Σ i, coords S Y A i) ≌ Lift.value Y A (pairSpan S) := by
  let _ (i : Nat × Nat) := cutEquivalence S Y A i
  let _ : (untag S).functor.IsIso := (untagIso S).isIso_functor
  let _ := Lift.equivOfIso (untag S) Y A
  exact ((ZeroPower.Sum.equiv fun i => (Lift.weighted (cut S i) Y A).asEquivalence).trans
    (collect (fixed S) Y A).asEquivalence).trans (Lift.weighted (untag S) Y A).asEquivalence
theorem native_at (i : Nat × Nat) : Sigma.incl (C := coords S Y A) i ⋙ (nativeEquiv S Y A).functor =
    Lift.weighted (Lift.comp (cut S i) (tagged S i)) Y A := by
  let C := Lift.weighted (cut S i) Y A
  have h := congrArg (C ⋙ ·) (collect_at (fixed S) Y A i)
  have k := Lift.weighted_comp (tag (fixed S) i) Y A (untag S)
  exact (congrArg (· ⋙ Lift.weighted (untag S) Y A) h).trans
    ((congrArg (C ⋙ ·) k).trans (Lift.weighted_comp (cut S i) Y A (tagged S i)))
noncomputable abbrev leaf (i : Nat × Nat) := CoproductSpan.All.component S Y A (i.1+i.2)
noncomputable def packedEquiv := (ZeroPower.Sum.equiv (leaf S Y A)).trans (PackedCuts.cutEquiv S Y A)
abbrev byLength := Sigma.desc (fun i : Nat × Nat => Sigma.incl (C := fun n => Lift.value Y A (power S n)) (i.1+i.2))
noncomputable abbrev iterates := ZeroPower.Sum.equiv (CoproductSpan.All.component S Y A)
theorem packed_join : (packedEquiv S Y A).functor ⋙ ((PackedFree.join S Y).app (op A)).toFunctor =
    byLength S Y A ⋙ (iterates S Y A).functor := by
  apply PackedFree.sigma_ext; intro i
  exact congrArg ((leaf S Y A i).functor ⋙ ·) (PackedCuts.cut_join_at S Y A i)
theorem native_join : (nativeEquiv S Y A).functor ⋙ Lift.weighted (two S) Y A =
    byLength S Y A ⋙ collect (power S) Y A := by
  apply PackedFree.sigma_ext; intro i
  exact (congrArg (· ⋙ Lift.weighted (two S) Y A) (native_at S Y A i)).trans
    ((Lift.weighted_comp (Lift.comp (cut S i) (tagged S i)) Y A (two S)).trans
      ((Lift.weighted_eq _ Y A (G := inclPower S (i.1+i.2)) (cut_rejoin S i)).trans (collect_at (power S) Y A (i.1+i.2)).symm))
/-- Equivalence obtained by retaining the two native cut lengths, evaluating
the whole native fixed-length string, and reconstructing the corresponding packed
cut. Neither the unrestricted row category nor an inverse to multiplication is used. -/
noncomputable def compare := (nativeEquiv S Y A).symm.trans (packedEquiv S Y A)
noncomputable abbrev evaluation := (CoproductSpan.All.evaluation S Y A).functor
noncomputable abbrev multiplication := ((PackedFree.monad S).μ.app Y).app (op A) |>.toFunctor
def pasteCuts {K R T V D W : Type*} [Category* K] [Category* R] [Category* T] [Category* V] [Category* D] [Category* W]
    (L : K ⥤ R) (M : R ⥤ W) (N : K ⥤ V) (U : V ⥤ T) (I : K ⥤ D) (C : D ≌ T) (J : D ⥤ W)
    (p : L ⋙ M = I ⋙ J) (q : N ⋙ U = I ⋙ C.functor) : L ⋙ M ≅ N ⋙ (U ⋙ (C.inverse ⋙ J)) :=
  eqToIso p ≪≫ isoWhiskerLeft I (isoWhiskerRight C.unitIso J) ≪≫ eqToIso (congrArg (· ⋙ (C.inverse ⋙ J)) q.symm)
def descend {K R T V : Type*} [Category* K] [Category* R] [Category* T] [Category* V]
    (N : K ≌ V) (E : K ⥤ R) (M : R ⥤ T) (J : V ⥤ T) (p : E ⋙ M ≅ N.functor ⋙ J) :
    (N.inverse ⋙ E) ⋙ M ≅ J := isoWhiskerLeft N.inverse p ≪≫ isoWhiskerRight N.counitIso J
noncomputable def coordSquare : (packedEquiv S Y A).functor ⋙ multiplication S Y A ≅
    (nativeEquiv S Y A).functor ⋙ Lift.weighted (two S) Y A ⋙ evaluation S Y A :=
  pasteCuts (packedEquiv S Y A).functor (multiplication S Y A) (nativeEquiv S Y A).functor
    (Lift.weighted (two S) Y A) (byLength S Y A) (collect (power S) Y A).asEquivalence (iterates S Y A).functor
    (packed_join S Y A) (native_join S Y A)
noncomputable def square : (compare S Y A).functor ⋙ multiplication S Y A ≅ Lift.weighted (two S) Y A ⋙ evaluation S Y A :=
  descend (nativeEquiv S Y A) (packedEquiv S Y A).functor (multiplication S Y A)
    (Lift.weighted (two S) Y A ⋙ evaluation S Y A) (coordSquare S Y A)
theorem actual : Lift.weighted (row S) Y A ⋙ FibreTotal.into Y (BlockCartesian.All.dest S) (BlockCartesian.All.source S) A ⋙
    BlockCartesian.All.onFibre S Y A ⋙ FibreTotal.out Y (rightLeg S) (leftLeg S) A = Lift.weighted (two S) Y A := by
  let F := NativeAssoc.Three.flattenOver S
  have k := Lift.back F Y A
  have j := Lift.weighted_comp (row S) Y A F
  have t := Lift.weighted_eq (Lift.comp (row S) F) Y A (G := two S) (two_flatten S)
  exact (congrArg (Lift.weighted (row S) Y A ⋙ ·) k).trans (j.trans t)
/-- The comparison uses the actual fibre functor of weighted native flattening,
the previous total-to-packed evaluation, and the multiplication of the packed monad. -/
noncomputable def actualSquare : (compare S Y A).functor ⋙ multiplication S Y A ≅
    Lift.weighted (row S) Y A ⋙ FibreTotal.into Y (BlockCartesian.All.dest S) (BlockCartesian.All.source S) A ⋙
      BlockCartesian.All.onFibre S Y A ⋙ FibreTotal.out Y (rightLeg S) (leftLeg S) A ⋙ evaluation S Y A :=
  square S Y A ≪≫ eqToIso (congrArg (· ⋙ evaluation S Y A) (actual S Y A).symm)
end ContextualComposition.GrothendieckStep.NativePacked
