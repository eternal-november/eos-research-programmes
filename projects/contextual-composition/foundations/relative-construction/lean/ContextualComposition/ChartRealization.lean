module
public import ContextualComposition.ChartRestriction
public import ContextualComposition.SuffixCell
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ChartRealization
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
section Move
variable {C D : Type*} [Category* C] [Category* D]
/-- Conjugate a previously specified action on all arrows by an objectwise chart. -/
def realize (F : C ⥤ D) {X : C → D} (l : ∀ x, X x ≅ F.obj x) : C ⥤ D where
  obj := X
  map {x y} f := (l x).hom ≫ F.map f ≫ (l y).inv
  map_id x := by simp
  map_comp _ _ := by simp
def gauge (F : C ⥤ D) {X : C → D} (l : ∀ x, X x ≅ F.obj x) : realize F l ≅ F :=
  NatIso.ofComponents l fun _ => by simp [realize]
def paste {F G : C ⥤ D} (c : F ≅ G) {X Z : C → D} (l : ∀ x, X x ≅ F.obj x) (r : ∀ x, Z x ≅ G.obj x) :
    realize F l ≅ realize G r := gauge F l ≪≫ c ≪≫ (gauge G r).symm
end Move
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
abbrev twice := (PackedFree.free S).obj ((PackedFree.free S).obj Y)
abbrev put (i : Nat × Nat) := ChainPayload.layerMap (PackedFree.inc S Y i.2) S i.1 ≫ PackedFree.inc S ((PackedFree.free S).obj Y) i.1
abbrev push (i : Nat × Nat) := ChainPayload.fibreMap (put S Y i) (𝟭 B)
abbrev Q (i : Nat × Nat) := Total Y (full S i).dest
noncomputable abbrev refL (i : Nat × Nat) := Lift.total (cut S i) Y ⋙ totalStages S Y i.1 i.2 ⋙ push S Y i
noncomputable abbrev refR (i : Nat × Nat) := global S Y (i.1+i.2) ⋙ BlockCompositor.transport (sameLength S Y i).symm ⋙ push S Y i
theorem reference (i : Nat × Nat) : refL S Y i = refR S Y i :=
  congrArg (· ⋙ push S Y i) (BlockCompositor.total S Y i.1 i.2)
variable (A : B)
abbrev source (i : Nat × Nat) := SpanPayload.Power.fibreInclude A Y (full S i).source (full S i).dest
noncomputable abbrev pack (i : Nat × Nat) := Sigma.incl (C := double S Y A) i ⋙ (packing S Y A).functor
theorem value_incl {G : WordTrace.Pr (B := B)} : FibreValue.value G A ⋙ FibreValue.incl G A = Functor.Fiber.fiberInclusion :=
  congrArg (· ⋙ Functor.Fiber.fiberInclusion) (FibreValue.value_embed G A)
theorem stagedIncl (i : Nat × Nat) :
    (staged S Y A i).functor ⋙ FibreValue.incl (family S Y i.1 i.2) A =
      SpanPayload.Power.fibreInclude A Y (fixed S i).source (fixed S i).dest ⋙ totalStages S Y i.1 i.2 := by
  let G := family S Y i.1 i.2
  let I := FibreTotal.into Y (fixed S i).dest (fixed S i).source A
  let K := onStrict S Y A i.1 i.2
  exact (congrArg (· ⋙ FibreValue.incl G A) (staged_global S Y A i.1 i.2)).trans
    ((congrArg (fun V => I ⋙ K ⋙ V) (value_incl A (G := G))).trans
      (congrArg (I ⋙ ·) (SpanPayload.fibre_diagram (totalStages S Y i.1 i.2) _ (totalOver S Y i.1 i.2) A)))
theorem packedObj (i : Nat × Nat) (x : double S Y A i) :
    (FibreValue.incl (twice S Y) A).obj ((pack S Y A i).obj x) =
      (push S Y i).obj ((FibreValue.incl (family S Y i.1 i.2) A).obj x) := rfl
theorem firstObj (i : Nat × Nat) (x : coords S Y A i) :
    (FibreValue.incl (twice S Y) A).obj ((pack S Y A i).obj ((first S Y A i).obj x)) =
      (refL S Y i).obj ((source S Y A i).obj x) := by
  have k := Functor.congr_obj (stagedIncl S Y A i) ((cutEach S Y A i).obj x)
  have b := Functor.congr_obj (Lift.global (cut S i) Y A) x
  exact (packedObj S Y A i _).trans
    ((congrArg (push S Y i).obj k).trans (congrArg (fun w => (push S Y i).obj ((totalStages S Y i.1 i.2).obj w)) b))
theorem leafIncl (i : Nat × Nat) :
    (leaf S Y A i).functor ⋙ FibreValue.incl (out S Y (i.1+i.2)) A =
      source S Y A i ⋙ global S Y (i.1+i.2) := by
  let n := i.1+i.2
  let H := global S Y n
  let I := FibreTotal.into Y (power S n).dest (power S n).source A
  let K := SpanPayload.fibreFunctor H _ (globalOver S Y n) A
  exact (congrArg (· ⋙ FibreValue.incl (out S Y n) A) (global_agrees S Y A n).symm).trans
    ((congrArg (fun V => I ⋙ K ⋙ V) (value_incl A (G := out S Y n))).trans
      (congrArg (I ⋙ ·) (SpanPayload.fibre_diagram H _ (globalOver S Y n) A)))
theorem transportIncl {G H : WordTrace.Pr (B := B)} (h : G = H) :
    BlockCompositor.revalue h A ⋙ FibreValue.incl H A =
      FibreValue.incl G A ⋙ BlockCompositor.transport h := by subst H; rfl
theorem secondObj (i : Nat × Nat) (x : coords S Y A i) :
    (FibreValue.incl (twice S Y) A).obj ((pack S Y A i).obj ((second S Y A i).obj x)) =
      (refR S Y i).obj ((source S Y A i).obj x) :=
  (packedObj S Y A i _).trans ((congrArg (push S Y i).obj (Functor.congr_obj
    (transportIncl A (sameLength S Y i).symm) ((leaf S Y A i).functor.obj x))).trans
    (congrArg (BlockCompositor.transport (sameLength S Y i).symm ⋙ push S Y i).obj (Functor.congr_obj (leafIncl S Y A i) x)))
end ContextualComposition.GrothendieckStep.ChartRealization
