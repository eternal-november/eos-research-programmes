module
public import ContextualComposition.NativeTrace
/-! The trace invariant identifies the independently staged evaluation and the original full-path evaluator before fibre restriction. Restrict, perform the arithmetic retag, and descend through the actual chart equivalence. Packed multiplication is used only afterwards to paste the new compositor to native flattening. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.BlockCompositor
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked BlockEvaluation WordTrace NativeTrace
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : Pr (B := B))
abbrev front (n m : Nat) := gradeProjection (Y := Y) (e := (fixed S (n,m)).dest) ⋙ Strict.fst (power S n).dest (power S m).source
abbrev back (n m : Nat) := gradeProjection (Y := Y) (e := (fixed S (n,m)).dest) ⋙ Strict.snd (power S n).dest (power S m).source
theorem stagesTrace (n m : Nat) (z : Edge (Total Y (fixed S (n,m)).dest)) :
    flattenRead S Y n m (Edge.map (totalStages S Y n m) z) =
    (word S n (Edge.map (front S Y n m) z) ++ word S m (Edge.map (back S Y n m) z),Edge.map (NativeTrace.leaf Y _) z) := by
  let U := suffix S Y n m
  let F := global S Y m
  let d := (power S m).dest
  let J := Strict.snd (power S n).dest (power S m).source
  let T := SpanPayload.totalMap Y J d rfl
  let h := read_global S (out S Y m) n (Edge.map U z)
  let a := congrArg (fun H => word S n (Edge.map H z)) (suffix_grade S Y n m)
  let b := congrArg (fun H => Edge.map H z) (suffix_boundary S Y n m)
  let c := read_global S Y m (Edge.map T z)
  let e : read S (out S Y m) n (Edge.map (totalStages S Y n m) z) =
      (word S n (Edge.map (front S Y n m) z),Edge.map F (Edge.map T z)) := h.trans (Prod.ext a b)
  unfold flattenRead
  rw [e]
  exact congrArg (fun w : Trace (P := P) Y => (word S n (Edge.map (front S Y n m) z) ++ w.1,w.2)) c
def transport {G H : Pr (B := B)} (h : G = H) : Total G (𝟭 B) ⥤ Total H (𝟭 B) := by subst H; exact 𝟭 _
theorem transport_edge {G H : Pr (B := B)} (h : G = H) (z : E G) : Edge.map (transport h) z = shift h z := by subst H; rfl
theorem shift_cancel {G H : Pr (B := B)} (h : G = H) (z : E G) : shift h.symm (shift h z) = z := by subst H; rfl
/-- Both uncurried evaluations agree after arithmetic transport of the output presheaf,
on the whole native source, including arrows moving the exterior and interior bases. -/
theorem total (n m : Nat) :
    Lift.total (cut S (n,m)) Y ⋙ totalStages S Y n m = global S Y (n+m) ⋙ transport (PackedCuts.sameLength S Y (n,m)).symm := by
  let C := Lift.total (cut S (n,m)) Y
  let h := PackedCuts.sameLength S Y (n,m)
  apply Edge.functor_ext
  intro z
  let w := Edge.map gradeProjection z
  let g := Edge.map (global S Y (n+m)) z
  let f := Edge.map (totalStages S Y n m) (Edge.map C z)
  have p := congrArg (fun H => Edge.map H z) (SpanPayload.total_projection Y (cut S (n,m)).functor _ (cut S (n,m)).dest)
  have k := word_cut S n m w
  have j := congrArg (fun H => Edge.map H z) (leaf_total Y (cut S (n,m)).functor _ (cut S (n,m)).dest)
  have l : (word S n (Edge.map (front S Y n m) (Edge.map C z)) ++ word S m (Edge.map (back S Y n m) (Edge.map C z))) =
      word S (n+m) w := (congrArg (fun t => word S n (Edge.map (Strict.fst (power S n).dest (power S m).source) t) ++
        word S m (Edge.map (Strict.snd (power S n).dest (power S m).source) t)) p).trans k
  have e : shift h f = g := read_injective S Y (n+m)
    ((read_order S Y n m f).trans ((stagesTrace S Y n m (Edge.map C z)).trans
      ((Prod.ext l j).trans (read_global S Y (n+m) z).symm)))
  exact (shift_cancel h f).symm.trans ((congrArg (shift h.symm) e).trans (transport_edge h.symm g).symm)
/-- Join as the actual inverse span map from strictly matched native blocks. -/
noncomputable def join (n m : Nat) : Nested.Over (fixed S (n,m)) (full S (n,m)) :=
  let c := blocks S n m
  ⟨c.joinFunctor,c.join_source,c.join_dest⟩
theorem join_cut (n m : Nat) : Lift.total (join S n m) Y ⋙ Lift.total (cut S (n,m)) Y = 𝟭 _ := by
  let J := join S n m
  let C := cut S (n,m)
  have e := SpanPayload.total_comp Y J.functor _ J.dest C.functor _ C.dest
  have k := (blocks S n m).strictIso.counit_eq
  exact e.trans (Lift.total_eq Y (d := (fixed S (n,m)).dest) (J := 𝟭 _) (k := rfl) k)
theorem onMatched (n m : Nat) : totalStages S Y n m =
    Lift.total (join S n m) Y ⋙ global S Y (n+m) ⋙ transport (PackedCuts.sameLength S Y (n,m)).symm :=
  (congrArg (· ⋙ totalStages S Y n m) (join_cut S Y n m).symm).trans
    (congrArg (Lift.total (join S n m) Y ⋙ ·) (total S Y n m))
def revalue {G H : Pr (B := B)} (h : G = H) (A : B) := (PackedCuts.ofCatIso ((eqToIso h).app (op A))).functor
theorem restrict_transport {X : Type*} [Category* X] {G H : Pr (B := B)} (h : G = H) (p : X ⥤ B)
    (F : X ⥤ Total G (𝟭 B)) (K : X ⥤ Total H (𝟭 B)) (j : K = F ⋙ transport h)
    (f : F ⋙ FibreValue.proj G = p) (k : K ⋙ FibreValue.proj H = p) (A : B) :
    SpanPayload.fibreFunctor K _ k A ⋙ FibreValue.value H A =
    SpanPayload.fibreFunctor F _ f A ⋙ FibreValue.value G A ⋙ revalue h A := by subst H; subst K; rfl
variable (A : B)
theorem fixedCompositor (n m : Nat) : CutCompositor.first S Y A (n,m) = CutCompositor.second S Y A (n,m) := by
  let U := cut S (n,m)
  let K := Lift.total U Y ⋙ totalStages S Y n m
  let F := global S Y (n+m)
  let T := PackedCuts.family S Y n m
  let I := NativeCleavage.FibreTotal.into Y (full S (n,m)).dest (full S (n,m)).source A
  have chain := fibreChain A (Lift.total U Y) (totalStages S Y n m) (Lift.over U Y) (totalOver S Y n m)
  have over := (congrArg (Lift.total U Y ⋙ ·) (totalOver S Y n m)).trans (Lift.over U Y)
  have c := restrict_transport (PackedCuts.sameLength S Y (n,m)).symm _ F K (total S Y n m) (globalOver S Y (n+m)) over A
  exact (congrArg (Lift.weighted U Y A ⋙ ·) (staged_global S Y A n m)).trans
    ((congrArg (· ⋙ onStrict S Y A n m ⋙ FibreValue.value T A) (Lift.into U Y A)).trans
    ((congrArg (fun H => I ⋙ H ⋙ FibreValue.value T A) chain).trans
    ((congrArg (I ⋙ ·) c).trans (congrArg (· ⋙ (PackedCuts.retag S Y A (n,m)).functor) (global_agrees S Y A (n+m))))))
noncomputable def compositor : CutCompositor.stages S Y A ≅ CutCompositor.previous S Y A :=
  CutCompositor.ofFixed S Y A (fun i => eqToIso (fixedCompositor S Y A i.1 i.2))
noncomputable def multiplicationSquare : CutCompositor.stages S Y A ⋙ multiplication S Y A ≅ CutCompositor.native S Y A :=
  isoWhiskerRight (compositor S Y A) (multiplication S Y A) ≪≫ actualSquare S Y A
theorem recovered : (CutCompositor.compositorOfSquare S Y A (multiplicationSquare S Y A)).hom = (compositor S Y A).hom := by
  apply (CutCompositor.compositorCells S Y A).injective
  exact CutCompositor.reconstructed S Y A _
end ContextualComposition.GrothendieckStep.BlockCompositor
