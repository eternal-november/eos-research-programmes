module
public import ContextualComposition.BoundaryPaste
@[expose] public section
namespace ContextualComposition.GrothendieckStep.BlockEvaluation
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativeCleavage NativePacked
open TelescopeSquares
set_option backward.isDefEq.respectTransparency false
universe u v k l
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
def totalPoints {K : Type*} [Category* K] (e : K ⥤ B) : Total Y e ≃ Σ k, Y.obj (op (e.obj k)) :=
  ⟨fun x => ⟨grade _ _ x,payload _ _ x⟩,fun z => pair _ _ z.1 z.2,fun _ => rfl,fun _ => rfl⟩
theorem injectTotal {K L : Type*} [Category* K] [Category* L] (r : K ⥤ L) (d : L ⥤ B) {e : K ⥤ B}
    (h : r ⋙ d = e) (j : Function.Injective r.obj) : Function.Injective (SpanPayload.totalMap Y r d h).obj := by
  subst e
  rintro ⟨⟨⟨x⟩,⟨a⟩⟩⟩ ⟨⟨⟨y⟩,⟨b⟩⟩⟩ k
  have v := congrArg (totalPoints Y d) k
  have z := j (congrArg Sigma.fst v)
  change x = y at z
  subst y
  exact congrArg (pair Y (r ⋙ d) x) (Sigma.mk.inj_iff.mp v).2.eq
def unpack (n : Nat) (x : Total (Evaluation.G S Y n) (𝟭 B)) : Evaluation.W S Y n :=
  let z := TelescopeSquares.unrealize Y S (n+1) (grade _ _ x) (payload _ _ x)
  pair Y _ ⟨grade _ _ x,z.1⟩ z.2
theorem unpack_eval (n : Nat) (x : Evaluation.W S Y n) : unpack S Y n ((Evaluation.functor S Y n).obj x) = x :=
  congrArg (fun z : Σ t : Chain P (n+1) (grade _ _ x).1, Y.obj (op (endpoint t)) =>
    pair Y (chainDest S n) ⟨(grade _ _ x).1,z.1⟩ z.2) (TelescopeSquares.unpack_pack Y S (grade _ _ x).2 (payload _ _ x))
theorem fixedInj (n : Nat) : Function.Injective (Evaluation.nativeFunctor S Y n).obj :=
  (Function.LeftInverse.injective (unpack_eval S Y n)).comp
    (injectTotal Y (powerComparison S n) _ (comparison_dest S n) (powerPoints S n).decode.injective)
def global : (n : Nat) → Total Y (power S n).dest ⥤ Total (PackedFree.pow S Y n) (𝟭 B)
  | 0 => 𝟭 _
  | n+1 => Evaluation.nativeFunctor S Y n
theorem globalOver : (n : Nat) → global S Y n ⋙ gradeProjection = gradeProjection ⋙ (power S n).source
  | 0 => rfl
  | n+1 => Evaluation.native_over S Y n
instance globalIso (n : Nat) : (global S Y n).IsIso := by
  cases n with
  | zero => exact (𝟭 _).asIsomorphism.isIso_functor
  | succ n =>
    change (Evaluation.nativeFunctor S Y n).IsIso
    exact { bijective_obj := ⟨fixedInj S Y n,Evaluation.native_obj_surj S Y n⟩ }
variable (A : B)
abbrev proj (n : Nat) := FibreTotal.projection Y (power S n).dest (power S n).source
def restrict (n : Nat) := FibreTotal.into Y (power S n).dest (power S n).source A ⋙
  SpanPayload.fibreFunctor (global S Y n) (FibreValue.proj (PackedFree.pow S Y n)) (globalOver S Y n) A ⋙
  FibreValue.value (PackedFree.pow S Y n) A
theorem fibreId {C D : Type*} [Category* C] [Category* D] (q : C ⥤ D) (x : D) :
    SpanPayload.fibreFunctor (𝟭 C) q (p := q) rfl x = 𝟭 _ :=
  EvalPayload.cancelInclusion _ _ (SpanPayload.fibre_diagram (𝟭 C) q rfl x)
set_option maxHeartbeats 1500000 in
theorem global_agrees : (n : Nat) → restrict S Y A n = (CoproductSpan.All.component S Y A n).functor
  | 0 => congrArg (fun H => FibreTotal.into Y (𝟭 B) (𝟭 B) A ⋙ H ⋙ FibreValue.value Y A) (fibreId (FibreValue.proj Y) A)
  | _+1 => rfl
abbrev out (n : Nat) := PackedFree.pow S Y n
noncomputable def suffix (n m : Nat) :=
  BoundaryPaste.fold Y (power S n).dest (power S m).source (power S m).dest (out S Y m) (global S Y m) (globalOver S Y m)
theorem suffix_grade (n m : Nat) : suffix S Y n m ⋙ gradeProjection = gradeProjection ⋙ Strict.fst (power S n).dest (power S m).source :=
  BoundaryPaste.fold_grade .. 
theorem suffix_boundary (n m : Nat) :
    suffix S Y n m ⋙ second (BoundaryPaste.projectionData (out S Y m)) (power S n).dest =
      SpanPayload.totalMap Y (Strict.snd (power S n).dest (power S m).source) (power S m).dest rfl ⋙ global S Y m :=
  BoundaryPaste.fold_suffix ..
theorem suffixOver (n m : Nat) : suffix S Y n m ⋙ FibreTotal.projection (out S Y m) (power S n).dest (power S n).source =
    FibreTotal.projection Y (fixed S (n,m)).dest (fixed S (n,m)).source :=
  congrArg (· ⋙ (power S n).source) (suffix_grade S Y n m)
theorem suffixIso (n m : Nat) : (suffix S Y n m).IsIso :=
  (BoundaryPaste.foldIso Y (power S n).dest (power S m).source (power S m).dest (out S Y m) (global S Y m) (globalOver S Y m)).isIso_functor
noncomputable def middle (n m : Nat) : Lift.value Y A (fixed S (n,m)) ⥤ Lift.value (out S Y m) A (power S n) :=
  FibreTotal.into Y (fixed S (n,m)).dest (fixed S (n,m)).source A ⋙ SpanPayload.fibreFunctor (suffix S Y n m) (proj S (out S Y m) n) (suffixOver S Y n m) A ⋙ FibreTotal.out (out S Y m) (power S n).dest (power S n).source A
def presentation {C D : Type*} [Category* C] [Category* D] (G : Dᵒᵖ ⥤ Cat.{l,k}) (d p : C ⥤ D) (x : D) :
    IsoCat (Total G (FibreTotal.endpoint d p x)) ((FibreTotal.projection G d p).Fiber x) where
  functor := FibreTotal.into G d p x
  inverse := FibreTotal.out G d p x
  unit_eq := (FibreTotal.into_out_functors G d p x).symm
  counit_eq := FibreTotal.out_into_functors G d p x
theorem middleEquivalence (n m : Nat) : (middle S Y A n m).IsEquivalence := by
  let _ := suffixIso S Y n m
  let _ := (suffix S Y n m).asIsomorphism.toEquivalence.isEquivalence_functor
  let F := FibreTotal.into Y (fixed S (n,m)).dest (fixed S (n,m)).source A
  let G := SpanPayload.fibreFunctor (suffix S Y n m) (proj S (out S Y m) n) (suffixOver S Y n m) A
  let H := FibreTotal.out (out S Y m) (power S n).dest (power S n).source A
  let _ : F.IsEquivalence := FibreTotal.intoEquivalence .. 
  let _ : G.IsEquivalence := SpanPayload.fibre_isEquivalence (suffix S Y n m) _ (suffixOver S Y n m) A (suffix S Y n m).bijective_obj.surjective
  let _ : H.IsEquivalence := (presentation (out S Y m) (power S n).dest (power S n).source A).symm.toEquivalence.isEquivalence_functor
  exact (F.asEquivalence.trans (G.asEquivalence.trans H.asEquivalence)).isEquivalence_functor
/-- Evaluate the actual suffix globally, then evaluate the prefix independently
with the resulting presheaf as payload. No evaluation of a joined path occurs. -/
noncomputable def staged (i : Nat × Nat) : Lift.value Y A (fixed S i) ≌ PackedCuts.double S Y A i := by
  let _ := middleEquivalence S Y A i.1 i.2
  exact (middle S Y A i.1 i.2).asEquivalence.trans (CoproductSpan.All.component S (out S Y i.2) A i.1)
noncomputable def tagsEquiv : (Σ i, Lift.value Y A (fixed S i)) ≌ Lift.value Y A (pairSpan S) := by
  let _ : (untag S).functor.IsIso := (untagIso S).isIso_functor
  let _ := Lift.equivOfIso (untag S) Y A
  exact (collect (fixed S) Y A).asEquivalence.trans (Lift.weighted (untag S) Y A).asEquivalence
noncomputable def blockwise := (tagsEquiv S Y A).symm.trans ((ZeroPower.Sum.equiv (staged S Y A)).trans (PackedCuts.packing S Y A))
/-- Staging before restricting the *outer* source: base arrows may move as well. -/
noncomputable def totalStages (n m : Nat) := suffix S Y n m ⋙ global S (out S Y m) n
theorem totalOver (n m : Nat) : totalStages S Y n m ⋙ FibreValue.proj (PackedCuts.family S Y n m) =
    FibreTotal.projection Y (fixed S (n,m)).dest (fixed S (n,m)).source :=
  (congrArg (suffix S Y n m ⋙ ·) (globalOver S (out S Y m) n)).trans (suffixOver S Y n m)
theorem totalIso (n m : Nat) : (totalStages S Y n m).IsIso := by
  let _ := suffixIso S Y n m
  exact ((suffix S Y n m).asIsomorphism.trans (global S (out S Y m) n).asIsomorphism).isIso_functor
noncomputable abbrev onStrict (n m : Nat) := SpanPayload.fibreFunctor (totalStages S Y n m) _ (totalOver S Y n m) A
theorem fibreChain {C D E T : Type*} [Category* C] [Category* D] [Category* E] [Category* T]
    {p : C ⥤ T} {q : D ⥤ T} {r : E ⥤ T} (a : T) (F : C ⥤ D) (G : D ⥤ E)
    (h : F ⋙ q = p) (k : G ⋙ r = q) :
    SpanPayload.fibreFunctor F q h a ⋙ SpanPayload.fibreFunctor G r k a = SpanPayload.fibreFunctor (F ⋙ G) r ((congrArg (F ⋙ ·) k).trans h) a := by
  apply EvalPayload.cancelInclusion
  exact (EvalPayload.fibrePaste a F G h k).trans (SpanPayload.fibre_diagram _ _ _ _).symm
theorem cancelMiddle {C D E M R T : Type*} [Category* C] [Category* D] [Category* E] [Category* M] [Category* R] [Category* T]
    (U : C ⥤ D) (H : D ⥤ E) (O : E ⥤ M) (I : M ⥤ E) (K : E ⥤ R) (V : R ⥤ T) (G : D ⥤ R)
    (e : O ⋙ I = 𝟭 _) (j : H ⋙ K = G) : (U ⋙ H ⋙ O) ⋙ (I ⋙ K ⋙ V) = U ⋙ G ⋙ V :=
  (congrArg (fun J => U ⋙ H ⋙ J ⋙ K ⋙ V) e).trans (congrArg (fun J => U ⋙ J ⋙ V) j)
theorem staged_global (n m : Nat) : (staged S Y A (n,m)).functor =
    FibreTotal.into Y (fixed S (n,m)).dest (fixed S (n,m)).source A ⋙ onStrict S Y A n m ⋙ FibreValue.value (PackedCuts.family S Y n m) A := by
  let U := FibreTotal.into Y (fixed S (n,m)).dest (fixed S (n,m)).source A
  let H := SpanPayload.fibreFunctor (suffix S Y n m) (proj S (out S Y m) n) (suffixOver S Y n m) A
  let I := FibreTotal.into (out S Y m) (power S n).dest (power S n).source A
  let O := FibreTotal.out (out S Y m) (power S n).dest (power S n).source A
  let K := SpanPayload.fibreFunctor (global S (out S Y m) n) (FibreValue.proj (PackedCuts.family S Y n m)) (globalOver S (out S Y m) n) A
  let V := FibreValue.value (PackedCuts.family S Y n m) A
  let G := onStrict S Y A n m
  have k := congrArg (middle S Y A n m ⋙ ·) (global_agrees S (out S Y m) A n).symm
  have e : O ⋙ I = 𝟭 _ := FibreTotal.out_into_functors .. 
  have j : H ⋙ K = G := fibreChain A (suffix S Y n m) (global S (out S Y m) n) (suffixOver S Y n m) (globalOver S (out S Y m) n)
  exact k.trans (cancelMiddle U H O I K V G e j)
theorem totalCartesian (n m : Nat) {a b : B} (f : a ⟶ b) {x y : Total Y (fixed S (n,m)).dest} (g : x ⟶ y) :
    (FibreTotal.projection Y (fixed S (n,m)).dest (fixed S (n,m)).source).IsStronglyCartesian f g ↔
    (FibreValue.proj (PackedCuts.family S Y n m)).IsStronglyCartesian f ((totalStages S Y n m).map g) := by
  let _ := totalIso S Y n m
  let _ := (totalStages S Y n m).asIsomorphism.toEquivalence.isEquivalence_functor
  exact SpanPayload.cartesian_iff _ _ (totalOver S Y n m) (totalStages S Y n m).bijective_obj.surjective f g
theorem totalPres (n m : Nat) {x y : Total Y (fixed S (n,m)).dest} (g : x ⟶ y) :
    Cartesian (FibreTotal.projection Y (fixed S (n,m)).dest (fixed S (n,m)).source) g →
    Cartesian (FibreValue.proj (PackedCuts.family S Y n m)) ((totalStages S Y n m).map g) :=
  Change.presOfStrong _ (totalOver S Y n m) (fun a f => (totalCartesian S Y n m a f).mp) g
section Choices
variable (n m : Nat) (L : Cleavage (FibreTotal.projection Y (fixed S (n,m)).dest (fixed S (n,m)).source))
  (J : Cleavage (FibreValue.proj (PackedCuts.family S Y n m)))
noncomputable abbrev baseFace {a b : B} (f : a ⟶ b) :=
  BlockCartesian.chosenFace _ _ (totalOver S Y n m) (totalPres S Y n m) L J f
theorem baseUnit : FibreValue.Paste.UnitLaw (F := onStrict S Y A n m) (X := Reindex.functor L (𝟙 A)) (Y := Reindex.functor J (𝟙 A))
    (baseFace S Y n m L J (𝟙 A)).sq (Route.unitIso L A).hom (Route.unitIso J A).hom := BlockCartesian.chosenUnit _ _ (totalOver S Y n m) (totalPres S Y n m) L J A
theorem baseComposition {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    FibreValue.Paste.CompLaw (F := onStrict S Y a n m) (G := onStrict S Y b n m) (H := onStrict S Y c n m)
      (X := Reindex.functor L f) (Y := Reindex.functor L g) (W := Reindex.functor L (f ≫ g))
      (X' := Reindex.functor J f) (Y' := Reindex.functor J g) (W' := Reindex.functor J (f ≫ g))
      (baseFace S Y n m L J (f ≫ g)).sq (baseFace S Y n m L J f).sq (baseFace S Y n m L J g).sq
      (Route.compIso L f g).hom (Route.compIso J f g).hom :=
  BlockCartesian.chosenComp _ _ (totalOver S Y n m) (totalPres S Y n m) L J f g
end Choices
/-- With an empty suffix, the independent suffix evaluation recovers the original
weighted word on actual global arrows, not just on a source fibre. -/
theorem emptySuffix (n : Nat) : Lift.total (cut S (n,0)) Y ⋙ suffix S Y n 0 = 𝟭 _ := by
  apply BoundaryPaste.fold_ext (power S n).dest Y
  · exact congrArg (Lift.total (cut S (n,0)) Y ⋙ ·) (suffix_grade S Y n 0)
  · exact congrArg (Lift.total (cut S (n,0)) Y ⋙ ·) (suffix_boundary S Y n 0)
theorem emptySuffixStages (n : Nat) : Lift.total (cut S (n,0)) Y ⋙ totalStages S Y n 0 = global S Y n :=
  congrArg (· ⋙ global S Y n) (emptySuffix S Y n)
theorem emptyPrefixStages (m : Nat) : totalStages S Y 0 m =
    SpanPayload.totalMap Y (Strict.snd (𝟭 B) (power S m).source) (power S m).dest rfl ⋙ global S Y m :=
  suffix_boundary S Y 0 m
end ContextualComposition.GrothendieckStep.BlockEvaluation
